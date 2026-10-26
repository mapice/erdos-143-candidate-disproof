# Revisione del 25 ottobre: struttura, notazione e Lean

Questa nota documenta la revisione del 25 ottobre. Dal 26 ottobre è disponibile
anche la [formalizzazione separata della prova logaritmica](Logarithmic-correspondence-2026-10-26.md),
conclusa dopo la stesura della presente nota.

La versione corrente ha 12 pagine; la precedente ne aveva 16. Il testo del
teorema principale è stato conservato identico, incluse tutte le costanti.
La revisione cambia l'organizzazione, riduce i simboli e sostituisce la
lunga esposizione analitica con una prova elementare più breve.

## Passo induttivo

La Proposizione 2.3 enuncia subito l'estensione di **ogni configurazione
ammissibile**, conservandone tutti i dati e guadagnando peso almeno `1/576`.
La prova del teorema principale segue immediatamente per iterazione di
questa stessa estensione. Non si assume di poter estendere qualunque
insieme finito separato: i vincoli aritmetici della Definizione 2.2 sono
parte essenziale dell'ipotesi.

La sottosezione 2.4 esplicita separatamente le quattro condizioni
conservate nell'induzione interna a un giro: ammissibilità e conservazione
dei dati; stessa griglia e prodotti dei primi abbastanza grandi; coprimalità
della griglia con i primi privati; incremento del peso. Il passaggio
`F₀ → D → pᵢ → E → Pᵢ → qᵢ → Aᵢ` rimane nello stesso ordine della prova.

## Corrispondenza dei simboli

| Testo corrente | Codice e manoscritto precedente | Ruolo |
| --- | --- | --- |
| `pᵢ` | `Hᵢ` / campo `H` | Primo privato del blocco |
| `qᵢ` | `Gᵢ` | Primo ausiliario, scelto dopo l'insieme finito |
| `pᵢ qᵢ` | precedente `pᵢ` | Modulo composto del filtro di residui |
| `pᵢ qᵢ − 1` | precedente `qᵢ` / campo denominatore `q` | Denominatore |
| `qᵢ Dᵢ n` | `Nᵢ,n` / campo `N` | Parte del numeratore che la griglia successiva assorbe |
| `Dᵢ n pᵢqᵢ/(pᵢqᵢ−1)` | `cᵢDᵢn`, valore dell'atomo formale | Punto inserito |

Il vincolo essenziale è scritto direttamente come `pⱼ ∤ qᵢDᵢn`.
La griglia successiva è un multiplo di tutti i prodotti `qᵢDᵢn` già
presenti e resta coprima a ogni primo privato. Nessuna parte del vincolo
è stata soppressa insieme al simbolo ausiliario.

Il testo non introduce più l'insieme `R(F,D)`. Il filtro effettivamente
usato fornisce la condizione più forte `|ka−Dn| > 1` per ogni intero `k`;
essa implica il predicato formale `RightFree`. Il margine `1/Bₐ` del vecchio
denominatore resta necessario e viene verificato prima di perturbare.

## Parte analitica

La nuova identità è

\[
\log|G_\chi(u,t)|=u\log|L(1+t,\chi)|+\Re R_\chi(u,t),
\qquad |R_\chi(u,t)|\le 1-u.
\]

Deriva dagli sviluppi assolutamente convergenti per `t>0`. Il controllo
è uniforme nel carattere, in `t` e in `0<u<1`; non usa una scelta globale
del logaritmo complesso né il non annullamento in `s=1`. Si ottiene la
stessa stima di Abel `liminf ≥ 1/(4L)` usata per l'estrazione finita.
Restano espliciti la convergenza prima dell'integrazione, i caratteri non
principali, le classi non invertibili, il modulo 1 e il termine `n=1`.
Nella riduzione alle classi invertibili è esplicitata l'identità
`1/(4dM) = 1/(4L)`, conservando la formulazione come stima inferiore
del limite inferiore.

**Questa nuova dimostrazione scritta non è stata sostituita alla prova Lean.**
Il codice conserva le disuguaglianze sui singoli fattori di Eulero e prova
lo stesso enunciato di selezione. La costruzione finita e l'enunciato
conclusivo restano quelli verificati. L'asintotica più forte ottenibile
con Selberg–Delange è documentata nella [nota dedicata](selberg-delange-review-2026-10-25.md),
non è usata nell'articolo e non è dichiarata formalizzata.

## Versioni e verifiche

- `paper/submitted-2026-10-23/`: PDF e sorgente esattamente corrispondenti
  alla versione inviata, conservati senza riscriverli.
- `paper/erdos143-candidate.tex` e `.pdf`: revisione corrente.
- `paper/revision-2026-10-25/`: diagnostica del PDF e controllo strutturale.
- 55 moduli Lean originari invariati; gli esiti formali precedenti restano
  attribuiti a quei sorgenti, senza dichiarare una nuova compilazione completa.
- L'identità del teorema principale, i riferimenti, le citazioni, i margini
  delle formule e tutte le 12 pagine renderizzate sono stati controllati.

La revisione è locale. Questi controlli non costituiscono un'accettazione
editoriale o una nuova revisione indipendente da parte di un esperto umano.


## Raffinamento della leggibilità

Una successiva passata applica i criteri di organizzazione della spiegazione
scientifica: scopo prima del calcolo, ruolo delle ipotesi vicino alla loro
introduzione, raccordi espliciti fra risultati. Il testo resta un articolo
di ricerca; non sono stati aggiunti esercizi o digressioni didattiche.

- La funzione di ciascuna condizione di ammissibilità è spiegata subito
  dopo la definizione.
- Il riassunto distingue i ruoli dei due primi. L'introduzione collega
  il primo privato alle posizioni da escludere sulla griglia successiva,
  anticipando il contenuto del lemma sulla griglia.
- Il blocco singolo e il giro completo sono distinti prima dell'iterazione
  infinita; il numero dei blocchi viene collegato alla perdita di densità
  e al guadagno di peso.
- Griglia ed etichette vengono identificate con `Dℓ` e `ℓ` prima del loro
  uso operativo; le due righe del filtro sono motivate separatamente.
  Il conteggio su un periodo comune, svolto per ciascun modulo separatamente,
  spiega perché non occorre coprimalità fra i moduli e perché ogni primo
  privato compare una sola volta nella stima.
- I vincoli sulla soglia dell'insieme primitivo sono collegati alle tre
  proprietà che devono garantire. I casi della separazione e la verifica
  dei vincoli aritmetici sono presentati in paragrafi distinti.
  Il blocco è definito prima di verificarne le proprietà; il passaggio
  da `F` a `F ∪ Aᵢ` è esplicitato alla conclusione del passo induttivo.
  La descrizione del filtro precisa che sono esclusi i multipli dei primi
  precedenti e del nuovo primo appena scelto.
- La parte analitica anticipa l'identità integrale e l'obiettivo di mediare
  i pesi dei livelli. L'ortogonalità compare prima dei limiti normalizzati,
  così il ruolo del carattere principale è visibile prima del calcolo.

Il teorema, la proposizione e i tre lemmi coincidono byte per byte con
la riscrittura precedente. La frase introduttiva della definizione è stata
precisata: l'ammissibilità riguarda la lista dei blocchi con i suoi dati,
non il solo insieme dei punti. Le quattro condizioni della definizione,
le formule e le costanti della dimostrazione non cambiano. Il PDF finale ha 12 pagine,
senza errori o avvisi di compilazione. Le pagine modificate sono state
ricontrollate visivamente; quelle invariate sono confrontate con le pagine
già osservate. La diagnostica corrente identifica l'ultima versione.


L'ulteriore rifinitura riduce le ripetizioni nel filtro, chiarisce che
`F₀` è l’insieme dei punti della configurazione iniziale, sostituisce il termine
“nested witnesses” con il riferimento diretto agli insiemi `F_R`, e rende
esplicito il contributo `κ_L/(4φ(L)) = 1/(4L)`. L'indice dei livelli
nella media geometrica è indicato come `r ≥ 0`. Il 25 ottobre l'autore ha
precisato il modello **GPT-6 Astra**; la dichiarazione IA della revisione
corrente è stata corretta. La dichiarazione contenuta nel PDF già inviato
è conservata senza alterazioni.


La sezione sulla formalizzazione è stata infine ordinata come segue:
risultati verificati, differenza fra le due prove analitiche, corrispondenza
fra costruzione e codice, riproduzione dei controlli. Ogni dichiarazione
Lean relativa alla costruzione è collegata alla propria funzione. La
descrizione degli assiomi distingue le dipendenze delle dimostrazioni dai
procedimenti con cui sono state controllate. Gli enunciati matematici,
le costanti e i sorgenti Lean restano invariati.


Sono inoltre esplicitati l'iniettività del passaggio dalle etichette ai
punti nella somma dei pesi, la definizione dell'insieme finale `F′` e la
scelta effettiva del sottoinsieme finito `P` nell'ultimo passo analitico.
Le condizioni sui parametri e la definizione di `f_r` sono disposte su
righe separate. Non cambia alcun enunciato o valore delle costanti.


La presentazione delle quattro conclusioni formali è raccolta in una tabella
che associa ciascun contenuto matematico al nome della dichiarazione Lean.
La formulazione reale è distinta dalla conclusione razionale rafforzata;
la riga del controllo supplementare esplicita l'unione dei medesimi insiemi
finiti. La tabella non amplia la portata dei risultati verificati.
