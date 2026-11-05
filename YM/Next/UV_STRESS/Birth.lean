import YM.Next.UV_STRESS.Grill
import YM.Next.UV_STRESS.Ration

/-!
# Coarse birth consumes continuum hierarchy's mask/flag costs

No independent βNpus in the joining estimate. Still a **trajectory-level**
price beginning at k (not parent Born theorem from singleton/equation
budgets; that physical work NOT done). Numerical inequalities exact; for an
E implementation the threshold and radius factors will have to pay this price
at the common stop.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Analysis Extraction Table Ward Lattice Wilson Overlay Marker Cells RG
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius
variable {G : Gauge} (C : Family G)
variable {N p ℓ k h m r : ℕ}

abbrev trays (C : Family G) (h p : ℕ) := Stock.census (Site (C.side h p))

structure TicketR where
  weight : ℝ
  stipend : 0 < weight
  u : ℝ
  c : ℝ
  b : ℝ
  d' : ℝ
  stop : ℕ

def TicketR.value (t : TicketR) (h d : ℕ) := Real.exp (Stock.expPrice C h t.stop d t.weight t.u t.c t.d' t.b)

/-- Exact red RG input per Grill precision. k,h and C prescribed. Quoted
weight & h powers across *one* mark per h copy. Active Bands demanded at all
intermediate steps; not an eventual continuum representation. The densities
have all subsets through the joined k. -/
structure Birth (T : TicketR) (t : h≤k) (ht : k ≤ N) (v : C.book.Token)
    (D : Config G (C.side k p) → ℝ) (A : Overlay.Lane C.path (trays C h p) N p) (L : Stair C (trays C h p) N p) : Prop where
  earlier : A.Works k
  fixed : A.load = fun _ => v.1
  uses (i) : A.uses i = (center C.S p (t.trans ht) 0).copy i (C.seen v (0:Site (C.side N p)))
  joined (s : (trays C h p).Mode) : L.echo C k s = consume C A (fun i => (center C.S p t 0).copy i (paint D)) s
  funded : L.Limit C k T.stop A.load
  stopped : (L.representation T.stop).Radial (fun _ => T.weight) T.u T.c T.d' T.b

lemma copy_safe {n : Side} (T : Tiling n) (F : Config G n → ℂ) (hp : Envelope F) (i : T.Cell) : Envelope (T.copy i F) := by
  classical
  obtain ⟨y,H⟩ := hp.cost
  let P := pull (K:=G.El) (T.omega i) (T.translateBy i)
  have ht : Measurable fun x => F (P x) := hp.meas.comp (continuous_pull ..).measurable
  by_cases h : T.hand i
  · simp_rw [show T.copy i F = fun x => star (F (P x)) from funext fun x => if_pos h]; exact ⟨(continuous_star.measurable.comp ht),y,fun x => by simp [H]⟩
  rw [show T.copy i F = fun x => F (P x) from funext fun x => if_neg h]; exact ⟨ht,y,fun x => H _⟩

lemma joined_law {t : h≤k} {hk : k ≤ N} {D : Config G (C.side k p) → ℝ}
    {A : Overlay.Lane C.path (trays C h p) N p} {L : Stair C (trays C h p) N p}
    {v T} (hp : C.Makes) (hD : Envelope (paint D)) (ht : Birth C T t hk v D A L) :
    Integrable (retrieve C t hk (paint D) (C.seen v (0:Site (C.side N p)))) (law G _ (C.beta N p)) ∧
    ‖moment (C.beta N p) (retrieve C t hk (paint D) (C.seen v (0:Site (C.side N p))))‖ ^
        ((Fintype.card (Site (C.side h p)) : ℝ)⁻¹) ≤ T.value C h v.1 := by
  let W := center C.S p t 0; let Y := center C.S p (t.trans hk) 0
  let J := fun (i : Site (C.side h p)) => W.copy i (paint D)
  have he (s) := serves_moments C A hp ht.earlier s J (fun i => copy_safe (G:=G) W _ hD i)
  let ξ (s) := moment (C.beta N p) (qualified C A s hk J)
  have h1 : L.Lit C k A.load ξ := by intro s; simp_rw [ht.joined]; exact (he s).2
  let I := Stock.final (Site (C.side h p))
  have hE : qualified C A I hk J=retrieve C t hk (paint D) (C.seen v (0:Site (C.side N p))) := by
    have he V : acquire C A I.val J V= removal C t hk (paint D) (C.seen v (0:Site (C.side N p))) V := by
      funext x; unfold acquire removal; simp_rw [ht.uses]; rfl
    unfold qualified retrieve; simp_rw [he]
  rw [← hE]; refine ⟨(he I).1,?_⟩
  exact lifted_spine (h:=h) C hp (ht.fixed ▸ ht.funded) (d:=v.1) (ht.fixed ▸ h1) ht.stopped T.stipend

/-- Putting a planned h with its actual numerical weight and terminal stop on
C should give this kind of price, if using the signed many-source path. Uses
F.late of *that extraction.* No hypothesis k=m cuts here.
-/
structure Invoice (F : Extraction.Order) (v : C.book.Token) (t : h≤k) (r : ℕ) (A : ℝ) (R : TicketR)
    (D : (N p : ℕ) → Config G (C.side k p) → ℝ) : Prop where
  amount : 0 ≤ A
  pays : F.late fun N p => ∃ H : k ≤ N,
    Interior (region (C.side k p) r) (paint (D N p)) ∧ (∀ x, |D N p x| ≤ A) ∧
      ∃ L X, Birth C R t H v (D N p) L X

lemma billed {F : Extraction.Order} {A ε : ℝ} {R : TicketR} {v : C.book.Token} {t : h≤k} {D}
    (hp : C.Makes) (hb : Invoice C F v t r A R D) (ht : R.value C h v.1 ≤ ε) : Coarse C F v t r A ε D := by
  refine ⟨hb.amount,?_⟩
  exact hb.pays.mono fun i hi => hi.mono fun j hj => by
    obtain ⟨hk,hP,H,L,X,hw⟩ := hj
    have hh := joined_law C hp (borel_bounded hP) hw
    exact ⟨hk,hP,H,hh.2.trans ht⟩
end YM.Next.UVStress
