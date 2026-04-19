with open('docs/05-类型理论/03-同伦类型论.md','r',encoding='utf-8') as f:
    text = f.read()

old = '[18] LICS HoTT Group. "Constructive Univalent Models in Grothendieck (∞,1)-Topoi". LICS 2025, 2025.\n\n---'
new = '[18] LICS HoTT Group. "Constructive Univalent Models in Grothendieck (∞,1)-Topoi". LICS 2025, 2025.\n\n[19] Voevodsky, V. "The Equivalence Axiom and Univalent Models of Type Theory". arXiv, 2010.\n\n---'
text = text.replace(old, new)

old2 = '[18] LICS HoTT Group. "Constructive Univalent Models in Grothendieck (∞,1)-Topoi". LICS 2025, 2025.\n\n##'
new2 = '[18] LICS HoTT Group. "Constructive Univalent Models in Grothendieck (∞,1)-Topoi". LICS 2025, 2025.\n\n[19] Voevodsky, V. "The Equivalence Axiom and Univalent Models of Type Theory". arXiv, 2010.\n\n##'
text = text.replace(old2, new2)

with open('docs/05-类型理论/03-同伦类型论.md','w',encoding='utf-8') as f:
    f.write(text)
print('Added ref 19')
