# Controllo della proposta Selberg–Delange

Data: 25 ottobre 2026. Oggetto: una possibile alternativa alla parte
analitica del manoscritto del 23 ottobre, ora abbreviata nella sezione 3
della revisione del 25 ottobre. La nota distingue la deduzione tramite
Selberg–Delange dalla prova elementare scelta per il testo e non modifica
i sorgenti Lean.

## Esito

La via Selberg–Delange è matematicamente applicabile. Una formulazione
precisa di Selberg–Delange permette di ottenere, per ogni modulo fissato,

\[
 A_{L,b}(u)=\frac{1}{L(1-u)}+O_L(1),\qquad u\uparrow1.
 \tag{1}
\]

Il limite esatto è quindi \(1/L\), e implica la stima sufficiente del
manoscritto con \(1/(4L)\). Tuttavia, rispetto alla versione breve che usa
direttamente i logaritmi dei prodotti di Eulero, questa strada richiede più
risultati esterni e non offre un vantaggio espositivo netto. **Raccomandazione:
conservare la prova elementare abbreviata e la stessa stima già usata nella
catena formale.** La formula (1) è qui una deduzione matematica distinta;
non viene presentata come risultato formalizzato.

## Fonte precisa per la strada Selberg–Delange

A. Granville e D. Koukoulopoulos, *Beyond the LSD method for the partial sums
of multiplicative functions*, Ramanujan J. **49** (2019), 287–319,
[DOI](https://doi.org/10.1007/s11139-018-0119-3),
[PDF degli autori](https://dms.umontreal.ca/~koukoulo/documents/publications/LSD.pdf).
Sono stati letti l'ipotesi (1.2), la definizione (1.3) e il **Teorema 1,
formula (1.5), a pagina 3 del PDF**. Nel PDF consultato non compare la
paginazione definitiva della rivista.

La specializzazione necessaria è la seguente. Se \(f\) è moltiplicativa,
\(|f|\leq1\), e

\[
 \sum_{p\leq x} f(p)\log p
 =\alpha x+O\bigl(x/(\log x)^{1/2}\bigr),
\]

allora

\[
 \sum_{n\leq x}f(n)
 =\frac{H_f(1)}{\Gamma(\alpha)}x(\log x)^{\alpha-1}
   +O\bigl(x/(\log x)^{1/2}\bigr),
 \qquad
 H_f(1)=\lim_{s\downarrow1}(s-1)^\alpha
                     \sum_{n\geq1}f(n)n^{-s}.
 \tag{2}
\]

Si prendono \(k=1\), \(A=1/2\), \(J=0\) nella fonte. La dipendenza delle
costanti è esplicita: soltanto \(k,A\) e la costante nell'ipotesi sui primi.
Questo punto permette l'applicazione uniforme seguente.

## Verifica delle ipotesi, compresi i caratteri non principali

Fissare prima il modulo \(q\), e porre, per \(1/2\leq u\leq1\),

\[
 f_{\chi,u}(n)=\chi(n)u^{\Omega(n)},\qquad
 S_\chi(x,u)=\sum_{n\leq x}f_{\chi,u}(n).
\]

Queste funzioni sono completamente moltiplicative, compreso il valore
zero sulle potenze dei primi divisori di \(q\); inoltre
\(|f_{\chi,u}(n)|\leq1=\tau_1(n)\).

Il teorema dei numeri primi nelle progressioni, a modulo fissato, fornisce

\[
 \sum_{p\leq x}\chi(p)\log p
 =\mathbf1_{\chi=\chi_0}x+
       O_q\bigl(x/(\log x)^{1/2}\bigr).
 \tag{3}
\]

Un riferimento leggibile direttamente è T. Tao,
[*254A, Notes 2: Complex-analytic multiplicative number theory*,
Exercise 64](https://terrytao.wordpress.com/2014/12/09/254a-notes-2-complex-analytic-multiplicative-number-theory/).
La formulazione lì riportata è più forte di quanto occorre. Per passare
dalla somma di von Mangoldt a (3), i termini \(p^j\leq x\), \(j\geq2\),
contribuiscono al più \(O(\sqrt{x}(\log x)^2)\); sommare poi sulle finitissime
classi invertibili con i pesi \(\chi\). I primi che dividono \(q\) sono
esclusi automaticamente. Il caso \(q=1\) è il teorema usuale sui primi.
Per \(q\) fissato, le costanti assorbono anche l'intervallo iniziale di \(x\).

Moltiplicare (3) per \(u\) non aumenta la costante dell'errore. Pertanto
(2) si applica con **una stessa costante per tutti gli \(u\in[1/2,1]\)**,
con

\[
 \alpha=u\quad(\chi=\chi_0),\qquad
 \alpha=0\quad(\chi\ne\chi_0).
\]

Per il principale si ottiene

\[
 S_{\chi_0}(x,u)=C_q(u)x(\log x)^{u-1}
                  +O_q\bigl(x/\sqrt{\log x}\bigr),
 \tag{4}
\]

dove

\[
 C_q(u)=\frac{1}{\Gamma(u)}
 \prod_{p\mid q}(1-p^{-1})^u
 \prod_{p\nmid q}\frac{(1-p^{-1})^u}{1-up^{-1}}.
 \tag{5}
\]

I logaritmi dei fattori del secondo prodotto sono \(O(p^{-2})\),
uniformemente in \(u\in[1/2,1]\); lo stesso vale per le loro derivate
rispetto a \(u\). Ne segue che \(C_q\) è continuamente differenziabile
su questo intervallo, con

\[
 C_q(1)=\prod_{p\mid q}(1-p^{-1})=\kappa_q=\varphi(q)/q,
 \qquad C_q(u)=\kappa_q+O_q(1-u).
 \tag{6}
\]

Per un carattere non principale, il coefficiente nella formula (2)
contiene \(1/\Gamma(0)=0\); quindi il termine principale scompare:

\[
 S_\chi(x,u)=O_q\bigl(x/\sqrt{\log x}\bigr)
 \quad(\chi\ne\chi_0),
 \tag{7}
\]

uniformemente nello stesso intervallo di \(u\). Questo giustifica
esplicitamente la cancellazione necessaria; non è una conseguenza della
sola applicazione del teorema al carattere principale.

## Dal conteggio al peso \(1/(n\log n)\)

Porre \(w(x)=1/(x\log x)\). Il termine \(n=1\) è presente in
\(S_\chi\), ma **va tolto prima** di applicare il peso:

\[
 J_\chi(u)=\int_2^\infty(S_\chi(x,u)-1)
                \frac{\log x+1}{x^2(\log x)^2}\,dx.
 \tag{8}
\]

Questa è la sommazione parziale della serie con \(n\geq2\). Il termine
al bordo superiore tende a zero, uniformemente per \(u\leq1\). L'errore
in (4) o (7), integrato in (8), è uniformemente limitato, perché

\[
 \int_2^\infty\frac{dx}{x(\log x)^{3/2}}<\infty.
\]

La parte principale di (4) dà precisamente

\[
 C_q(u)\left\{
  \frac{(\log2)^{u-1}}{1-u}
 +\frac{(\log2)^{u-2}}{2-u}\right\}.
\]

Per \(u\uparrow1\), il secondo addendo è limitato e
\(((\log2)^{u-1}-1)/(1-u)\) resta limitato. Di conseguenza

\[
 J_{\chi_0}(u)=\frac{\kappa_q}{1-u}+O_q(1),
 \qquad J_\chi(u)=O_q(1)\quad(\chi\ne\chi_0).
 \tag{9}
\]

La convergenza assoluta delle serie pesate, per ogni \(u<1\), segue
applicando (4) al modulo uno: il coefficiente è nonnegativo e la parte
principale integrata è finita. La stessa serie nonnegativa domina quella
di ogni carattere; per \(0\leq u<1/2\) basta la dominazione mediante il
caso \(u=1/2\). Sono quindi leciti anche i riordinamenti successivi.

Per \((c,q)=1\), ortogonalità e (9) implicano

\[
 A_{q,c}(u)=\frac{1}{\varphi(q)}
       \sum_{\chi\bmod q}\overline{\chi(c)}J_\chi(u)
 =\frac1{q(1-u)}+O_q(1).
 \tag{10}
\]

Il modulo uno comprende un solo carattere e rientra nella stessa formula.

## Resti non coprimi e cambiamento del logaritmo

Prendere \(0\leq b<L\), \(d=(b,L)\), \(q=L/d\), \(c=b/d\), con
\((0,L)=L\). La corrispondenza è \(n=dm\),
\(m\equiv c\pmod q\), e \((c,q)=1\), anche per \(q=1\).
L'identità \(\Omega(dm)=\Omega(d)+\Omega(m)\) **non richiede**
\((d,m)=1\).

Per \(m\geq2\),

\[
 0\leq\frac1{m\log m}-\frac1{m\log(dm)}
 \leq\frac{\log d}{m(\log m)^2}.
\]

La serie del membro destro converge per confronto integrale e non
dipende da \(u\). L'unico eventuale termine omesso, \(m=1\), è presente
esattamente quando \(d\geq2\) e \(c\equiv1\pmod q\); vale
\(u^{\Omega(d)}/(d\log d)\), dunque è limitato. Se \(d=1\), quel
termine corrisponde a \(n=1\) ed è correttamente escluso.
Pertanto

\[
 A_{L,b}(u)=\frac{u^{\Omega(d)}}d A_{q,c}(u)+O_L(1).
\]

Inserire (10) e usare
\(u^{\Omega(d)}=1+O_L(1-u)\) dà (1). Il modulo è fissato prima
del limite; questa deduzione non afferma alcuna uniformità utile per
\(L\to\infty\).

## Confronto con la prova breve elementare

Per \(t>0\), gli sviluppi assolutamente convergenti dei logaritmi dei
prodotti di Eulero danno

\[
 \log|G_\chi(u,t)|
 =u\log|L(1+t,\chi)|+\Re R_\chi(u,t),
 \quad
 R_\chi(u,t)=\sum_p\sum_{j\geq2}
       \frac{(u^j-u)\chi(p)^j}{j p^{j(1+t)}}.
\]

Non occorre scegliere una determinazione di \(\log L\) a \(s=1\):
si usano gli sviluppi assoluti per \(s>1\) e poi le parti reali.
Poiché \(|u^j-u|\leq(j-1)(1-u)\),

\[
 |R_\chi(u,t)|
 \leq(1-u)\sum_p\sum_{j\geq2}\frac{j-1}{j p^j}
 \leq(1-u)\sum_{m\geq2}\frac1{m(m-1)}
 =1-u.
 \tag{11}
\]

La continuità dei \(L\) non principali sulla semiretta reale basta
quindi a limitare \(G_\chi\), uniformemente in \(u\). Per il principale,
\(tL(1+t,\chi_0)\to\kappa_q\). La stessa relazione (11) dà anche
\(G_1(u,t)\ll t^{-u}\) vicino a zero; per \(t\geq1\),
\(|G_\chi(u,t)-1|\ll2^{-t}\). Questi sono esattamente i controlli
necessari a Tonelli e all'estrazione mediante medie di Abel.

Per mantenere la costante già in uso, è sufficiente osservare che, per
\(u\geq1/2\), \(e^{\Re R}\geq e^{-1/2}>1/2\), e scegliere
\(\varepsilon>0\) con \(tL(1+t,\chi_0)\geq\kappa_q/2\) per
\(0<t\leq\varepsilon\). Allora

\[
 \liminf_{u\uparrow1}(1-u)
       \int_0^\infty(G_{\chi_0}(u,t)-1)\,dt
 \geq\frac{\kappa_q}{4}.
\]

Questa prova usa solo l'analisi sulla semiretta reale già richiesta
nel manoscritto. Non richiede (3), il teorema dei numeri primi nelle
progressioni, né \(L(1,\chi)\ne0\). Il passo per \(d=(b,L)\) e
l'estrazione di un insieme primitivo finito restano gli stessi per
entrambe le strade.

La selezione, in particolare, non richiede che *tutti* i livelli
\(\Omega(n)=r\) siano pesanti. La stima di Abel basta a trovare livelli
arbitrariamente alti di peso maggiore di \(1/6\); ciascun livello è
primitivo e un suo sottoinsieme finito mantiene la disuguaglianza stretta.
Il taglio \(N\) si ottiene scegliendo \(r\) con \(2^r\geq N\).

## Cautele sulla citazione e scelta editoriale

- Non basta citare un'asintotica per ciascun \(u<1\) separatamente:
  senza controllo uniforme, la soglia da cui parte l'asintotica potrebbe
  crescere con \(u\) in modo incompatibile con il limite.
- I caratteri non principali vanno trattati con esponente singolare
  \(\alpha=0\), come in (7); non condividono il termine principale del
  carattere principale.
- Il solo teorema per coefficienti nonnegativi non si applica direttamente
  alle serie dei caratteri non principali. Il Teorema 1 citato ammette
  coefficienti complessi e risolve questo punto.
- Una citazione alternativa verificata è B. Chang e G. Martin,
  [*The smallest invariant factor of the multiplicative group*](https://arxiv.org/abs/1908.00035v2),
  Appendice A: Definizioni A.4/A.6, Teorema A.13 e Corollario A.14
  (pp. 17–18 e 23–24 del PDF). Il Corollario A.14 riguarda coefficienti
  nonnegativi e può coprire il principale; per gli altri caratteri si
  devono ancora verificare prolungamento analitico, scelta dei logaritmi
  e crescita in una regione priva di zeri. Non è una scorciatoia rispetto
  al Teorema 1 sopra applicato.

Accogliere l'obiezione espositiva del referee non impone dunque di
cambiare la struttura della dimostrazione. La sostituzione delle lunghe
stime locali con (11), seguita dai pochi passaggi realmente necessari,
fornisce una risposta più economica e conserva il risultato analitico
già collegato alla formalizzazione. Non viene avanzata qui alcuna nuova
affermazione di novità bibliografica o di verifica formale.
