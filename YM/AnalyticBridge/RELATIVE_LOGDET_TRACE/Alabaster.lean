import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Fresco
import YM.AnalyticBridge.RELATIVE_LOGDET_TRACE.Year

/-!
# Group on original bond words

Exact projected sums and costs. For G gauges in Schur grouping don't
assume that particular colors select; pass through the unconditional
series before determinant identities. Doesn't assert gauge symmetry of an
arbitrary mark's tested values; only of underlying determinant letters.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.RelativeLogdet.Paint
open Filter Function Set Matrix MeasureTheory FreeResolvent Next.SectorChange
open  RG
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {ι κ γ : Type} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
variable {A B : Square (ι × κ)} {H : ι → Square κ}
variable {W : ι→ Set ι} {D : Cost γ} {p : ι × κ→γ} {v C q : ℝ} {m : ℕ}

def string (P S : Square (ι × κ)) (i j : ι) (x : Fin m→ι) : Square κ := Matrix.of fun u v=>
    ∑ a : Fin m→κ, road P S (i,u) (j,v) fun n=>(x n,a n)

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma length_succ (P S : Square (ι × κ)) (i j : ι) (x : Fin (m+1)→ι) : string P S i j x=block P i (x 0) * string S S (x 0) j (Fin.tail x) := by
  ext u v
  rw [string,of_apply, sum_cons, Matrix.mul_apply]; apply Finset.sum_congr rfl; intro z _
  rw [string,of_apply,Finset.mul_sum]
  apply Finset.sum_congr rfl; intro a _; rw [road,Fin.cons_zero]
  congr 2

omit [Fintype ι] [DecidableEq ι] in
lemma unison {P S : Square (ι×κ)} (hq : Moves H) (h : Elation H A B) (hs : Elation H P S) (i j : ι) (x : Fin m→ι) :
    string B S i j x=H i*string A P i j x*(H j).transpose := by
  induction m generalizing A B i with
  | zero=>
    have hv (A P : Square (ι×κ)) : string A P i j x=block A i j := Matrix.ext fun i j=> by simp [string,block,road]
    rw [hv,hv]; exact h ..
  | succ n ih=> rw [length_succ,length_succ,h,ih hs]; exact Elation.rectangle hq ..

variable {n : ℕ}
abbrev paints (κ : Type) (z : Letter ι n) := κ × (Fin (z.1+n)→κ)

def hue (z : Letter ι n) (c : paints κ z) : Letter (ι×κ) n :=
  ⟨z.1,(z.2.1,c.1),fun i=>(z.2.2 i,c.2 i)⟩

def braid (f : Letter (ι × κ) n → ℝ) (z : Letter ι n) := ∑ i : paints κ z, f (hue z i)

lemma braid_err (z : Letter ι 0) (A : Square (ι×κ)) (W : ι→Set ι) :
    let S := -excess (all W) A
    braid (errata (all W) A) z= - Matrix.trace (string S S z.2.1 z.2.1 z.2.2)/ ((z.1:ℝ)+1) := by
  intro S; unfold braid Matrix.trace string; rw [Fintype.sum_prod_type]
  simp only [errata,hue, Matrix.diag_apply, of_apply]
  simp_rw [← Finset.sum_div, Finset.sum_neg_distrib]; rfl

lemma braid_scroll (z : Letter ι 1) (A : Square (ι × κ)) (W : ι→Set ι) (t : ℝ) :
    let f w := scroll (all W) A (hue z w).2.1 (hue z w).2.2 t
    (∑ w : paints κ z, f w)= - Matrix.trace (string (pie (all W) A t) (-defect (all W) A t) z.2.1 z.2.1 z.2.2) := by
  intro f; unfold Matrix.trace string; rw [Fintype.sum_prod_type]
  simp_rw [f,scroll, Finset.sum_neg_distrib]; rfl

lemma braid_page (z : Letter ι 1) (h : Priced D p (all W) A v C q) :
    braid (page (all W) A) z=∫ u in Ioi 0, - Matrix.trace (string (pie (all W) A u) (-defect (all W) A u) z.2.1 z.2.1 z.2.2) := by
  unfold braid page
  rw [← integral_finsetSum _ (fun i _=> (h.scroll_paid (hue z i)).1)]
  exact setIntegral_congr_fun measurableSet_Ioi fun u _=> braid_scroll z A W u

def batch (f : ι × κ → ℝ) (i : ι) := ∑ j,f (i,j)
lemma braid_reg (i : ι) (h : Priced D p (all W) A v C q) :
    batch (letterBase (all W) A) i=∫ u in Ioi 0, ((Fintype.card κ:ℝ)*attenuation u-Matrix.trace (block (pie (all W) A u) i i)) := by
  unfold batch letterBase; rw [← integral_finsetSum _ (fun j _=> (h.regular_price (i,j)).1)]
  simp_rw [Finset.sum_sub_distrib, Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; rfl

lemma grouped_same (h : Priced D p (all W) A v C q) (h' : Priced D p (all W) B v C q) (hv : Moves H) (hw : ∀ i,i∈W i)
    (he : Elation H A B) :
    batch (letterBase (all W) A)=batch (letterBase (all W) B) ∧
      braid (page (all W) A)=braid (page (all W) B) ∧ braid (errata (all W) A)=braid (errata (all W) B) := by
  refine ⟨funext fun i=>?_,funext fun z=>?_,funext fun z=>?_⟩
  · rw [braid_reg _ h,braid_reg _ h']; refine setIntegral_congr_fun measurableSet_Ioi fun u hu=> ?_
    rw [caught W hw hv he h.gram u hu.out.le,Elation.relaxed hv]
  · rw [braid_page z h,braid_page z h']; refine setIntegral_congr_fun measurableSet_Ioi fun u hu=>?_
    rw [unison hv (caught W hw hv he h.gram u hu.out.le) (circles W hw hv he h.gram u hu.out.le).opposite,Elation.relaxed hv]
  have hs := (cursed W hw hv he h.gram).opposite
  rw [braid_err z,braid_err z, unison hv hs hs, Elation.relaxed hv]

section sales
variable {c : Lattice.Side}
open Lattice

def dye (ι κ : Type) (n : ℕ) : (Σ i : Letter ι n, paints κ i) ≃ Letter (ι × κ) n where
  toFun x:= hue x.1 x.2
  invFun x:= ⟨⟨x.1,x.2.1.1,fun i=>(x.2.2 i).1⟩, x.2.1.2,fun i=>(x.2.2 i).2⟩
  left_inv _:= rfl
  right_inv _:= rfl
omit [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ] in
lemma displacements (p : ι→Site c) (l B m : ℕ) (r : Fin m→κ) (s : Fin m→ι) (i j : ι × κ) :
    pocket (fun i : ι×κ=>p i.1) l B i j (fun x=>(s x,r x))=pocket p l B i.1 j.1 s := by
  induction m generalizing i with
  | zero=>rfl
  | succ m ih=> rw [pocket,pocket]; have ht:= ih (Fin.tail r) (Fin.tail s) (s 0,r 0); rw [← ht]; rfl

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma reconciling {f : Letter (ι × κ) n → ℝ} (hf : Summable f) :
    HasSum (braid f) (∑' i,f i) := by
  exact (((dye ι κ n).hasSum_iff).mpr hf.hasSum).sigma (fun x=> hasSum_fintype _)
omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma genuine (f : Letter (ι × κ) n→ℝ) (p : ι→Site c) (B l : ℕ) (a s : ℝ)
    (h : Ac.Hit (inventory (fun i : ι×κ=>p i.1) l B) B f a s) : Ac.Hit (inventory p l B) B (braid f) a s := by
  intro x
  let t := fun i : Letter (ι×κ) n=> if x∈inventory (fun i : ι×κ=>p i.1) l B i then f i*Real.exp (a*coverNumber B (inventory (fun i : ι×κ=>p i.1) l B i)) else 0
  have hf : SumBudget t s := h x
  have hp : SumBudget (braid t) s := ⟨fun i=> Finset.sum_nonneg fun j _=> hf.1 _,(reconciling hf.2.1).summable,
    (reconciling hf.2.1).tsum_eq.trans_le hf.2.2⟩
  convert hp using 2 with i
  unfold braid t
  have hh w : inventory (fun i : ι×κ=>p i.1) l B (hue i w)=inventory p l B i := displacements _ _ _ _ _ _ _ _
  simp_rw [hh]; split <;> simp only [*,Finset.sum_mul,Finset.sum_const_zero]

omit [Fintype ι] [DecidableEq ι] [DecidableEq κ] in
lemma marginals {f g : Letter (ι×κ) n → ℝ} (h : ∀ i,|f i| ≤ g i) (i : Letter ι n) : |braid f i| ≤ braid g i :=
  (Finset.abs_sum_le_sum_abs ..).trans (Finset.sum_le_sum fun _ _=>h _)


end sales
end YM.AnalyticBridge.RelativeLogdet.Paint

namespace YM.AnalyticBridge.RelativeLogdet.Physical
open Paint Function Set Matrix MeasureTheory FreeResolvent Next.SectorChange
open  RG Wilson Pressure Tree Precision Lattice
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S}
    {A : Stores S} (F : Forest S.ratio) (k : S.Choices) {V : Config G c} {x v C η b : ℝ}
    (hT : Certified S T x v C η b)
include hT

/-- The three letter data types, when used at the gauge-invariant value
level. Use `Paint.genuine` and `Paint.marginals` to retain the SAME hit
budget as for all micro letters. Must use all colors (not asserting each
summand braiding them is invariant). -/
theorem gilded (z : Site c→ G.El) (hS : S.patch.Branches S.kernel G) (hp : A.flags=RG.flags (temp x) V)
    {o : Clip} {s u M : ℝ} (ht : T.up.Bounds o s u M) :
    let P:=AFull T A F x V k; let Q:=AFull T A F x (gauge z V) k; let W:=windows S x (G:=G)
    batch (letterBase W P)=batch (letterBase W Q) ∧
      braid (page W P)=braid (page W Q) ∧ braid (errata W P)=braid (errata W Q) := by
  intro P Q W
  have he : A.flags= RG.flags (temp x) (gauge z V) := by simpa using hp
  let bW : Bond f→Set (Bond f) := fun i=>{j | meeting S x i j}
  have hh : Moves (clockface S z) := fun i=>banner_spins (G:=G) (z (S.ratio.parent i.1))
  have hx : ∀ i,i∈bW i := fun i => by -- no Colors needed
    intro p hp q hq
    have hi := meetings i hp; have hj := meetings i hq
    apply (separation_triangle p (S.ratio.parent i.1) q).trans
    rw [separation_comm p]; apply le_trans (Nat.add_le_add hi hj); have H:=hT.basis; omega
  exact grouped_same (W:=bW) (hT.text A F k V hp |>.2.2.2) (hT.text A F k _ he |>.2.2.2) hh hx (gauge_elation z V k T hS x A F ht)
end YM.AnalyticBridge.RelativeLogdet.Physical
