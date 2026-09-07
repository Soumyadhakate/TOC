from flask import Flask, render_template, request, jsonify, Response
import random, json, csv, io

app = Flask(__name__)

EPS = {"", "ε", "ϵ", "epsilon", "eps"}

def parse_items(s):
    return list(dict.fromkeys(x.strip() for x in s.replace(";", ",").split(",") if x.strip()))

def is_eps(s):
    return s.strip().lower() in EPS

def tokenize(s, variables, terminals):
    s=s.strip()
    if is_eps(s): return []
    symbols=sorted(set(variables+terminals), key=len, reverse=True)
    if any(c.isspace() for c in s):
        parts=s.split()
        if all(p in symbols for p in parts): return parts
        out=[]
        for p in parts: out += tokenize(p,variables,terminals)
        return out
    out=[]; i=0
    while i<len(s):
        hit=next((x for x in symbols if s.startswith(x,i)),None)
        if hit is None: raise ValueError(f"Unknown symbol near: {s[i:]}")
        out.append(hit); i+=len(hit)
    return out

def parse_grammar(d):
    V=parse_items(d.get("variables","")); T=parse_items(d.get("terminals","")); S=d.get("start","").strip()
    if not V: raise ValueError("Enter at least one variable.")
    if not T: raise ValueError("Enter at least one terminal.")
    if S not in V: raise ValueError("Start variable must be in Variables.")
    if set(V)&set(T): raise ValueError("Variables and terminals cannot overlap.")
    rules={v:[] for v in V}
    text=d.get("productions","").replace("→","->")
    for line in text.splitlines():
        line=line.strip()
        if not line: continue
        if "->" not in line: raise ValueError(f"Invalid production: {line}")
        lhs,rhs=line.split("->",1); lhs=lhs.strip()
        if lhs not in V: raise ValueError(f"Unknown variable: {lhs}")
        for alt in rhs.split("|"):
            for part in alt.split("/"):
                rules[lhs].append(tokenize(part,V,T))
    if not any(rules.values()): raise ValueError("Enter production rules.")
    return {"variables":V,"terminals":T,"start":S,"rules":rules}

def clone(g):
    return {"variables":g["variables"][:],"terminals":g["terminals"][:],"start":g["start"],
            "rules":{a:[r[:] for r in g["rules"].get(a,[])] for a in g["variables"]}}

def dedupe(rs):
    out=[]; seen=set()
    for r in rs:
        k=tuple(r)
        if k not in seen: seen.add(k); out.append(r[:])
    return out

def rstr(r): return " ".join(r) if r else "ε"
def text(g):
    return "\n".join(f"{a} → " + " | ".join(rstr(r) for r in g["rules"].get(a,[]))
                     for a in g["variables"] if g["rules"].get(a))

def nullable(g):
    n=set()
    changed=True
    while changed:
        changed=False
        for a in g["variables"]:
            if a in n: continue
            for r in g["rules"].get(a,[]):
                if not r or all(x in n for x in r):
                    n.add(a); changed=True; break
    return n

def eliminate_epsilon(g):
    n=nullable(g); out=clone(g)
    for a in g["variables"]:
        new=[]
        for r in g["rules"].get(a,[]):
            if not r: continue
            pos=[i for i,x in enumerate(r) if x in n]
            for mask in range(1<<len(pos)):
                q=[x for i,x in enumerate(r) if i not in pos or not(mask & (1<<pos.index(i)))]
                if q: new.append(q)
        out["rules"][a]=dedupe(new)
    if g["start"] in n: out["rules"][g["start"]]=dedupe(out["rules"][g["start"]]+[[]])
    return out, ("Nullable: "+", ".join(sorted(n))) if n else "No epsilon productions found."

def eliminate_unit(g):
    out=clone(g); V=g["variables"]
    closure={a:{a} for a in V}
    changed=True
    while changed:
        changed=False
        for a in V:
            for r in g["rules"].get(a,[]):
                if len(r)==1 and r[0] in V:
                    before=len(closure[a]); closure[a]|=closure[r[0]]
                    changed |= len(closure[a])>before
    for a in V:
        out["rules"][a]=dedupe([r for b in closure[a] for r in g["rules"].get(b,[])
                                if not(len(r)==1 and r[0] in V)])
    return out,"Unit productions A → B removed."

def eliminate_useless(g):
    gen=set(); changed=True
    while changed:
        changed=False
        for a in g["variables"]:
            if a in gen: continue
            if any(all(x in g["terminals"] or x in gen for x in r) for r in g["rules"].get(a,[])):
                gen.add(a); changed=True
    reach={g["start"]}; changed=True
    while changed:
        changed=False
        for a in list(reach):
            for r in g["rules"].get(a,[]):
                for x in r:
                    if x in gen and x in g["variables"] and x not in reach:
                        reach.add(x); changed=True
    useful=gen&reach; out=clone(g)
    out["variables"]=[a for a in g["variables"] if a in useful]
    out["rules"]={a:[r for r in g["rules"].get(a,[]) if all(x in g["terminals"] or x in useful for x in r)]
                  for a in out["variables"]}
    removed=[a for a in g["variables"] if a not in useful]
    return out,("Removed: "+", ".join(removed)) if removed else "No useless symbols found."

def fresh(a,used):
    x=a+"'"
    while x in used: x+="'"
    used.add(x); return x

def eliminate_left_recursion(g):
    V=g["variables"][:]; used=set(V); rules={a:[r[:] for r in g["rules"].get(a,[])] for a in V}; extra=[]
    for i,A in enumerate(V):
        for B in V[:i]:
            expanded=[]
            for r in rules[A]:
                if r and r[0]==B:
                    for q in rules[B]: expanded.append(q+r[1:])
                else: expanded.append(r)
            rules[A]=dedupe(expanded)
        alpha=[r[1:] for r in rules[A] if r and r[0]==A]
        beta=[r for r in rules[A] if not(r and r[0]==A)]
        if alpha:
            Apr=fresh(A,used); extra.append(Apr)
            rules[A]=[b+[Apr] for b in (beta or [[]])]
            rules[Apr]=[a+[Apr] for a in alpha]+[[]]
    out={"variables":V+extra,"terminals":g["terminals"][:],"start":g["start"],"rules":{}}
    out["rules"]={a:dedupe(rules.get(a,[])) for a in out["variables"]}
    return out,("Created: "+", ".join(extra)) if extra else "No left recursion detected."

def pipeline(g):
    steps=[("Original Grammar",g,"Original grammar entered.")]
    for name,fn in [("1. Epsilon Production Elimination",eliminate_epsilon),
                    ("2. Unit Production Elimination",eliminate_unit),
                    ("3. Useless Symbol Elimination",eliminate_useless),
                    ("4. Left Recursion Elimination",eliminate_left_recursion)]:
        g,d=fn(g); steps.append((name,g,d))
    return steps,g

# ---------- parse tree ----------
def nnode(s,failed=False): return {"symbol":s,"children":[],"failed":failed}

def leaves(n):
    if not n["children"]: return [n]
    z=[]
    for c in n["children"]: z+=leaves(c)
    return z

def copytree(n):
    return {"symbol":n["symbol"],"children":[copytree(c) for c in n["children"]],"failed":n.get("failed",False)}

def target_tokens(s,g):
    if not s.strip(): return []
    if any(c.isspace() for c in s): 
        q=s.split()
        return q if all(x in g["terminals"] for x in q) else None
    out=[]; i=0
    for _ in range(len(s)+1):
        if i>=len(s): return out
        hit=next((t for t in sorted(g["terminals"],key=len,reverse=True) if s.startswith(t,i)),None)
        if not hit:return None
        out.append(hit);i+=len(hit)
    return None

def parse_tree(g,target):
    root=nnode(g["start"]); queue=[([g["start"]],root)]; seen=set(); limit=30000
    while queue and len(seen)<limit:
        syms,tr=queue.pop(0); key=tuple(syms)
        if key in seen: continue
        seen.add(key)
        if all(x in g["terminals"] for x in syms):
            if syms==target:return True,tr
            continue
        pos=next((i for i,x in enumerate(syms) if x in g["variables"]),None)
        if pos is None:continue
        prefix=[]
        for x in syms:
            if x in g["terminals"]:prefix.append(x)
            else:break
        if target[:len(prefix)]!=prefix:continue
        A=syms[pos]
        for r in g["rules"].get(A,[]):
            ns=syms[:pos]+r+syms[pos+1:]
            if sum(x in g["terminals"] for x in ns)>len(target):continue
            nt=copytree(tr); ls=leaves(nt)
            if pos>=len(ls):continue
            ls[pos]["children"]=[nnode("ε")] if not r else [nnode(x) for x in r]
            queue.append((ns,nt))
    return False,None

def attempted_tree(g,target):
    root=nnode(g["start"]); syms=[g["start"]]
    for _ in range(25):
        pos=next((i for i,x in enumerate(syms) if x in g["variables"]),None)
        if pos is None:break
        A=syms[pos]; choices=g["rules"].get(A,[])
        if not choices:break
        def score(r):
            q=syms[:pos]+r+syms[pos+1:]
            return sum(i<len(q) and i<len(target) and q[i]==target[i] for i in range(min(len(q),len(target))))
        r=max(choices,key=score); ls=leaves(root)
        if pos>=len(ls):break
        ls[pos]["children"]=[nnode("ε")] if not r else [nnode(x) for x in r]
        syms=syms[:pos]+r+syms[pos+1:]
    ls=leaves(root)
    if ls:
        next((x for x in reversed(ls) if x["symbol"] in g["variables"]),ls[-1])["failed"]=True
    return root

def gen_one(g,maxlen):
    cur=[g["start"]]
    for _ in range(300):
        vars=[i for i,x in enumerate(cur) if x in g["variables"]]
        if not vars:
            return cur if len(cur)<=maxlen else None
        i=random.choice(vars); r=random.choice(g["rules"].get(cur[i],[]))
        q=cur[:i]+r+cur[i+1:]
        if sum(x in g["terminals"] for x in q)<=maxlen and len(q)<=maxlen+len(g["variables"])+15:cur=q
    return None

@app.route("/")
def home(): return render_template("index.html")

@app.post("/api/analyze")
def analyze():
    try:
        g=parse_grammar(request.json or {}); steps,final=pipeline(g)
        return jsonify({"success":True,"steps":[{"name":a,"grammar":text(b),"details":c} for a,b,c in steps],
                        "final_grammar":text(final),"grammar":g})
    except Exception as e:return jsonify({"success":False,"error":str(e)}),400

@app.post("/api/check")
def check():
    try:
        d=request.json or {}; g=parse_grammar(d); start=d.get("parseStart","").strip() or g["start"]
        if start not in g["variables"]:raise ValueError("Parse start variable is not defined.")
        g["start"]=start; target=target_tokens(d.get("testString",""),g)
        if target is None:return jsonify({"success":True,"valid":False,"message":"Input contains a symbol that is not a declared terminal.","tree":attempted_tree(g,[])})
        ok,tr=parse_tree(g,target)
        if ok:return jsonify({"success":True,"valid":True,"message":"Complete parse tree generated from the grammar.","tree":tr})
        return jsonify({"success":True,"valid":False,"message":"String is not generated by this grammar. The tree shows an attempted parse.","tree":attempted_tree(g,target)})
    except Exception as e:return jsonify({"success":False,"error":str(e)}),400

@app.post("/api/generate")
def generate():
    try:
        d=request.json or {};g=parse_grammar(d);count=max(1,min(5000,int(d.get("sampleCount",50))));ml=max(1,min(100,int(d.get("maxLength",20))))
        data=[];seen=set()
        for _ in range(max(1000,count*100)):
            if len(data)>=count:break
            r=gen_one(g,ml)
            if r is None:continue
            s=" ".join(r)
            if s not in seen:seen.add(s);data.append({"string":s,"length":len(r)})
        return jsonify({"success":True,"data":data,"requested":count})
    except Exception as e:return jsonify({"success":False,"error":str(e)}),400

@app.post("/api/download")
def download():
    d=request.json or {};fmt=d.get("format","txt");data=d.get("dataset",[])
    if fmt=="json": content=json.dumps(data,indent=2,ensure_ascii=False);mime="application/json";fn="grammar_dataset.json"
    elif fmt=="csv":
        o=io.StringIO();w=csv.writer(o);w.writerow(["No","Generated String","Length"])
        for i,x in enumerate(data,1):w.writerow([i,x.get("string",""),x.get("length","")])
        content=o.getvalue();mime="text/csv";fn="grammar_dataset.csv"
    else: content="\n".join(x.get("string","") for x in data);mime="text/plain";fn="grammar_dataset.txt"
    return Response(content,mimetype=mime,headers={"Content-Disposition":f"attachment; filename={fn}"})

if __name__=="__main__":
    app.run(debug=True,host="127.0.0.1",port=5000)
