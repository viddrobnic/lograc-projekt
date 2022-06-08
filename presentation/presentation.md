---
marp: true

theme: gaia
paginate: true
backgroundColor: #fff
---

<style>
  :root {
    --color-background: #fff;
    --color-foreground: #1e1e1e;
    --color-highlight: #027acc;
    --color-dimmed: #1e1e1e;
  }
</style>

<!-- _class: lead -->

# 2–3 trees

Vid Drobnič, Matej Marinko

---

# 2-3 Trees

TODO slikce / risanje po tabli

---

# 2-3 Trees

- INF set
- TODO dokazi so zraven

![bg left:60%](2-3tree.png)

---

# 2-3 Trees

![bg left:60%](example.png)

---

# Search

- Relation $a \in t$

![bg right:60%](element.png)

---

<style>
  :root {
    --color-background: #eee;
    --color-foreground: #1e1e1e;
    --color-highlight: #027acc;
    --color-dimmed: #1e1e1e;
  }
</style>

# Search

- Relation $a \in t$
- Decidable type
- Search function
- Lemmas to eliminate impossible cases

![bg right:60%](search.png)

---

# Insert

- Proofs that $a$ lies between bounds
- Height of the tree can increase
- Defined recursively
- Some cases cannot happen

![bg left:60%](insert.png)

---

# Obstacles Encountered

- Overly complicated Tree definition at the beginning led us to rewrite code using $\leqslant$ instead of $<$.
- Inserting _might_ increase the height of the tree.
- `insert` cannot return certain values.
- `insert` also returns a proof $a \in t$.

---

# What Remains to be Done

- Write wrapper for `insert` function.
- Restructure the code to use Agda modules.
