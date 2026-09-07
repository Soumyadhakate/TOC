# GrammarSynth Flask

Run on Windows:

```powershell
python -m venv venv
venv\Scripts\activate
pip install -r requirements.txt
python app.py
```

Open http://127.0.0.1:5000/

Test:
Variables: S, A, B
Terminals: a, b
Start: S
Productions:
S->aAB
A->bBb/bb
B->A/ϵ

Check `abb`.
