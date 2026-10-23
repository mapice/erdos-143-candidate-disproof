# Corrispondenza fra articolo e Lean

Controllo locale del 23 ottobre 2026. I 55 moduli della prova del 2 ottobre
sono conservati senza modifiche. `ManuscriptAudit.lean` espone ulteriormente
gli enunciati dell'articolo; non sostituisce la compilazione o il controllo
degli assiomi del progetto completo.

| Affermazione dell'articolo | Dichiarazione Lean | Controllo di significato |
| --- | --- | --- |
| Coppie ordinate distinte e ogni moltiplicatore intero positivo | `Original`, `constructedSet_original` | I quantificatori coprono entrambe le direzioni; `k : ℕ`, `1 ≤ k`. |
| Insieme razionale contenuto in `[2,∞)` | `mainConclusion_proved`, `constructedSet_lower` | Nessuna ipotesi analitica o costruttiva residua nell'enunciato conclusivo. |
| Somma dei pesi divergente | `constructedSet_weight_diverges` | Somma in `ENNReal` uguale a `⊤`; non valore convenzionale di una `tsum` reale non sommabile. |
| Conclusione esplicita nel dominio reale | `realConclusion_proved` | Razionalità, numerabilità, separazione, somma nonnegativa infinita e `¬ Summable` espliciti. |
| Nessun punto di accumulazione finito | `strongConclusion_proved`, `original_locallyFiniteAbove` | Ogni intervallo iniziale limitato contiene finiti punti; il limite inferiore è 2. |
| Vicinanza positiva a un intero, esponente 12 | `constructedSet_tiny` | Esiste `m ≥ 2`, con `0 < a-m ≤ 1/(2*m^12)`. |
| Stessa successione di prefissi, inclusione e guadagno | `pointSequence_monotone`, `stateSequence_mass_lower` | Gli stessi stati ricorsivi definiscono `constructedSet`; guadagno non stretto `R/576`. |
| Numerabile infinito | `manuscript_full_statement` nel supplemento | Numerabilità e `A.Infinite` sono campi espliciti dello stesso enunciato. L'infinità è dedotta dalla divergenza e dalla finitezza dei pesi; i teoremi originali restano invariati. |
| Selezione primitiva periodica | `periodicPrimitiveSelection_proved` | Periodo positivo fissato prima della selezione, densità `> 2/3`, soglia arbitraria `N ≥ 2`, peso finito `> 1/6`. |
| Residui anche non invertibili | `all_residues_abel_lower_bound` | Riduzione mediante `gcd`, additività di `Ω` e errore logaritmico sommabile; non richiede coprimalità fra i fattori. |
| Inserimento finito senza spostare i punti | `insert_block_exists`, `block_extension_valid` | Prima `H`, poi filtro e insieme finito `P`, infine `G`; gli invarianti sono dimostrati insieme. |
| Reset della griglia | `state_grid_exists`, `state_grid_free` | Griglia divisibile per ogni vecchia parte non privata del numeratore, coprima ai primi privati. |
| Costo di densità per blocco | `root_not_bad_separated`, moduli `RootResidues` e `RoundLabels` | Filtro chiuso sufficiente per l'intervallo semiaperto; confronto mediante unione finita, senza indipendenza. |
| Round completo e unione infinita | `round_extension_exists`, `stateSequence`, `constructedSet` | Ogni round conserva gli atomi precedenti e aumenta il peso di almeno `1/576`. |

Il termine `dilation-separated` dell'articolo è definito dalla stessa
formula del predicato Lean `Original`; il precedente manoscritto lo chiamava
`original`. Tutti i nomi di dichiarazione sono nello spazio `Erdos143`. I dettagli delle
interfacce analitiche e costruttive sono in `docs/Abel-periodic-proof.md` e
`docs/Construction-correspondence.md`.

## Passaggi ricalcolati nella rilettura matematica

- Il prodotto correttivo finito è `2M/(M+1) < 2`; la stima dei fattori complessi usa l'identità esatta `|1-uz|² = (1-u)+u|1-z|²-u(1-u)|z|²`.
- Il limite di Abel inferiore per una classe è `1/(4L)`. Sommandolo su una densità `> 2/3` si ottiene una massa normalizzata `> 1/6`.
- Un limite superiore eventuale `f_r ≤ 1/6` per gli strati contraddirebbe la stima di Abel. Si ottengono arbitrariamente molti strati sufficientemente alti, non un limite inferiore per ogni strato.
- Il costo complessivo del filtro è minore di `1/100 + 1/4 = 13/50`; la densità ammessa supera `37/50`, che supera `2/3` di `11/150`.
- La griglia rende il divario un multiplo intero non nullo di `a/H > 4` quando il primo privato non divide l'etichetta. Se lo divide, si ha una collisione esatta: l'esclusione della classe zero è giustificata in entrambe le direzioni.
- L'intervallo semiaperto esclude `ka-m` in `(-1,1]`. La discrezione del vecchio denominatore e `η < 1/B_a` preservano il divario dopo lo spostamento positivo, per tutti i moltiplicatori contemporaneamente.
- Primitività all'interno del blocco, ordine fra blocchi e controllo delle vecchie sorgenti trattano tutti i tipi di coppia; non manca la direzione nuova sorgente/vecchio bersaglio.
- Da `q ≥ 2U^13` e `m ≤ U` segue `m/q ≤ (1/2)m^(-12)`.
- Da `n ≥ 2D`, `1 < c < 2`, segue `log(cDn) ≤ 2 log n`, quindi `w(cDn) ≥ w(n)/(4D)` e un guadagno per blocco `> 1/(24D)`.
- `floor(D/12) ≥ D/24` per `D ≥ 48`; il guadagno per round è almeno `1/576`. La monotonia dei prefissi dà la divergenza sull'unione.

Questa è una rilettura locale assistita dall'IA nell'ambito della preparazione
dell'articolo. Non costituisce una revisione indipendente, una verifica di
priorità esaustiva o un giudizio editoriale della rivista.

Il controllo supplementare `Erdos143.manuscript_full_statement`, compilato il
23 ottobre 2026, riunisce inoltre un solo insieme `A` e una sola successione
`F : ℕ → Finset ℚ`: numerabilità, infinità, limite inferiore 2, separazione,
somma infinita, finitezza degli intervalli iniziali razionali, piccoli
spostamenti positivi, monotonia e separazione dei prefissi, peso `R/576`
e identità dell'unione. La finitezza degli intervalli iniziali razionali
esclude anche accumulazioni reali finite: ogni intervallo reale limitato
è contenuto in un intervallo iniziale con estremo razionale.
Il controllo degli assiomi di questo ulteriore corollario restituisce
soltanto `propext`, `Classical.choice` e `Quot.sound`.
