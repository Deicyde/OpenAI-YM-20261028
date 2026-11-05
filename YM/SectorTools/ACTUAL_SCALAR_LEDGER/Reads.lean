import YM.AnalyticBridge.GAUSSIAN_FIELD_ALIGNMENT.Gauges
import YM.AnalyticBridge.RESET_INCOME_PORT.Cohort
import YM.AnalyticBridge.RESET_INCOME_PORT.LogQuote
import YM.AnalyticBridge.RESET_INCOME_PORT.Sheen
import YM.AnalyticBridge.SECTOR_COVARIANCE_JETS.Sale
import YM.Further.GAUSSIAN_SCALAR_LEDGER.Hitting
import YM.Next.MAXWELL.Det
import YM.Next.ROTATIONS.Fold
import YM.Next.ROTATIONS.Mode
import YM.Progress.DIRECTED_RECIPE.Symmetry
import YM.SectorNext.LARGE_FIELD_REMAINDERS.Reprice
import YM.SectorTools.ACTUAL_SCALAR_LEDGER.Matrix
import YM.UVNext.COUPLING_RESET.Compare

set_option warningAsError false
set_option autoImplicit false
set_option synthInstance.maxSize 1024

/-!
# True local value dependence of the paired anchor-window debit

Compare LITERAL arrays at two Plates (x and path tube fixed, not necessarily fixed forest,
fields or stores). Common positions only, not asserting that the error or whole chargeOut
has that support. Beware that the remaining exponent/additive activities require several
other query neighborhoods and growth/absolute analysis. SectorChange's endpoint window here
is tree-independent before selecting Free: complete on the trunks too with identity to
run the local comparison using Covariance.Terrain's sharp lookup on this same prescription.
No bounds or rates should be spent at mismatched flag tables just from this equality, and
in particular this result is not about de-masking such fields.
-/
noncomputable section
namespace YM.SectorTools.ActualScalar.Locations
open Function Filter Set MeasureTheory Matrix RG Wilson Lattice Pressure Pressure.Stores Bid Precision Tree Push.SectorMeasure
  Next.SectorChange Further GaussianScalar AnalyticBridge.ResetIncome SectorNext.Vacuum AnalyticBridge Covariance.Terrain
open scoped Topology BigOperators Classical ContDiff Matrix.Norms.Frobenius

private lemma powers {ι ρ : Type} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ] (v : ι ↪ ρ)
    (X : Wall ρ) (hX : ∀ i j, j ∉ range v → X (v i) j=0) (n : ℕ) :
    (X^n).submatrix v v = (X.submatrix v v)^n := by
  induction n with
  | zero => rw [pow_zero,pow_zero,submatrix_one _ v.injective]
  | succ n ih =>
    rw [pow_succ',pow_succ',←ih]; ext i j
    rw [submatrix_apply,Matrix.mul_apply,Matrix.mul_apply,← Finset.sum_subset (s₁:=Finset.univ.image v) (Finset.subset_univ _) _, Finset.sum_image (g:=v) v.injective.injOn]
    · rfl
    intro j _ hj; rw [hX i _ (by simpa [range] using hj),zero_mul]

private lemma bead_book {ι ρ : Type} [Fintype ι] [DecidableEq ι] [Fintype ρ] [DecidableEq ρ] (v : ι ↪ ρ)
    (X : Wall ρ) (hX : ∀ i j, j ∉ range v → X (v i) j=0) (i : ι) (L : ℝ) :
    Panel.priceLine (X.submatrix v v) L i = Panel.priceLine X L (v i) := by
  unfold Panel.priceLine Panel.bead; congr 1; apply tsum_congr; intro n
  have hl : Panel.stencil (X.submatrix v v) L = (Panel.stencil X L).submatrix v v := by simp [Panel.stencil,submatrix_sub,submatrix_one _ v.injective,submatrix_smul]
  have hz (i j) (hj : j∉range v) : Panel.stencil X L (v i) j=0 := by
    unfold Panel.stencil; rw [Matrix.sub_apply,Matrix.one_apply_ne (fun hh => hj ⟨_,hh⟩),Matrix.smul_apply,hX i j hj,smul_zero,sub_zero]
  rw [hl, ← powers v _ hz]; rfl

variable {G : Gauge} {c f : Side} {S : StepData c f} (e : Plate G S) (h : Doors e)
    (A : Stores S) (t : S.Choices) (V : Config G c)

def key : Key e.forest G ↪ Covariance.Atom G f := (Embedding.subtype (· ∉ e.forest.trunks)).prodMap (.refl _)

def onto (hb : 120 ≤ radiusB e.x) (i : Key e.forest G) : ↥((frame e hb).eye i) ↪ ↥(unitWin S e.x (key e i)) where
  toFun j := ⟨key e j.val, (eye_test e hb j.val i).mp j.property⟩
  inj' := fun _ _ hh => Subtype.ext ((key e).injective (congr_arg Subtype.val hh))

variable {e}
lemma trunk_zero (i j : Covariance.Atom G f) (hj : j.1∈e.forest.trunks) (hi : i≠j) :
    scanA e.tube A e.forest t e.x V i j=0 := by
  have h (k) : scanD e.tube A e.forest t e.x V k j=0 := if_neg (fun h : onStage A e.forest e.x j.1 => h.1 hj)
  unfold scanA shard; rw [Matrix.add_apply,diagonal_apply_ne _ hi,Matrix.mul_apply]; simp [h]

lemma off (hb i) (j : ↥(unitWin S e.x (key e i))) (hj : j ∉ range (onto e hb i)) : j.val.1∈e.forest.trunks := by
  by_contra h; let k : Key e.forest G := (⟨j.val.1,h⟩,j.val.2)
  exact hj ⟨⟨k,(eye_test ..).mpr j.property⟩,Subtype.ext rfl⟩

variable (Y : GaussianScalar.Frozen (held e A) G)
lemma scan_restrict : (page e h A t V).sigma Y = (scanA e.tube A e.forest t e.x V).submatrix (key e) (key e) := by
  let Q := (page e h A t V).sigma Y
  let X := scanA e.tube A e.forest t e.x V
  let C := e.Gram A V t; let L := GaussianFieldAlignment.live A e.forest e.x (G:=G) (S:=S)
  have he : Q = GaussianFieldAlignment.fill L C := sigma_fill ..
  let u := splitKey e A
  let ht := Completion.sorted A e.forest (x:=e.x) (G:=G)
  let v (j : Hold G (held e A)) : Completion.vacant A e.forest e.x G := ⟨(j.1.val.val,j.2), fun ⟨i,hi⟩ => ?missed⟩
  have hp (j : Hold G (held e A)) : key e (u (Sum.inr j)) = ht (Sum.inr (v j)) := rfl
  have hq i : key e (u (Sum.inl i)) = ht (Sum.inl i) := rfl
  have hs := GaussianFieldAlignment.fill_read L C u (live_eq e A)
  have hZ : X.submatrix ht ht = Completion.wide C 1 := backA ..
  ext i j
  obtain ⟨i,rfl⟩ := u.surjective i; obtain ⟨j,rfl⟩ := u.surjective j
  rw [show (page e h A t V).sigma Y=Q from rfl, he, show GaussianFieldAlignment.fill L C (u i) (u j)=_ from congr_fun (congr_fun hs i) j]
  cases i <;> cases j <;> simp only [submatrix_apply,hq,hp]
  next i j => exact (congr_fun (congr_fun hZ (.inl i)) (.inl j)).symm
  next i j => exact (congr_fun (congr_fun hZ (.inl i)) (.inr (v j))).symm
  next i j => exact (congr_fun (congr_fun hZ (.inr (v i))) (.inl j)).symm
  next i j =>
    rw [show scanA _ _ _ _ _ _ _ _ =_ from congr_fun (congr_fun hZ (.inr (v i))) (.inr (v j))]
    by_cases hv : i=j
    · subst i; simp [Completion.wide]
    have hh : v i ≠ v j := fun h => hv (Prod.ext (Subtype.ext (Subtype.ext (congr_arg Prod.fst (congr_arg Subtype.val h)))) (congr_arg (fun k => (Subtype.val (α:=Bond f × G.ColorIndex) k).2) h))
    simp [Completion.wide,hv,hh]
  case missed =>
    have hx : j.1.val = i.1.val := Subtype.ext (congr_arg Prod.fst hi)
    exact i.1.property (hx ▸ ((held_iff e A j.1.val).mp j.1.property))

variable (hb : 120 ≤ radiusB e.x) (i : Key e.forest G) (L : ℝ)
lemma self (x : ℝ) (hx : 120 ≤ radiusB x) (p : Covariance.Atom G f) : p ∈ unitWin S x p := by
  intro y hy z hz
  let o := Covariance.Terrain.home S p
  have h1 : separation y o ≤ 1 := (separation_comm ..).trans_le (meetings (S:=S) _ hy)
  have h2 : separation o z ≤ 1 := meetings (S:=S) _ hz
  apply (separation_triangle y o z).trans; omega

def linePay (T : Tube G S) (A : Stores S) (F : Forest S.ratio) (t : S.Choices) (V : Config G c) (x : ℝ)
    (hx : 120 ≤ radiusB x) (p : Covariance.Atom G f) (L : ℝ) :=
  Panel.priceLine (Schur.principal (scanA T A F t x V) (unitWin S x p)) L ⟨p,self x hx p⟩

lemma local_scan : let u := page e h A t V; let b := frame e hb
    b.localLine (u.sigma Y) L i = linePay e.tube A e.forest t V e.x hb (key e i) L := by
  intro u b; let W := Schur.principal (scanA e.tube A e.forest t e.x V) (unitWin S e.x (key e i))
  have he : b.glass (u.sigma Y) i = W.submatrix (onto e hb i) (onto e hb i) := by unfold u Lens.glass; rw [scan_restrict]; rfl
  rw [Lens.localLine,he]
  have hx (p j) (hj : j ∉ range (onto e hb i)) : W (onto e hb i p) j=0 := trunk_zero A t V _ _ (off _ _ j hj)
    (fun hh => hj ⟨p,Subtype.ext hh⟩)
  exact bead_book _ W hx (b.center i) _

section compare
variable (T : Tube G S) (A' : Stores S) (F F' : Forest S.ratio) (t' : S.Choices) (V' : Config G c) (x : ℝ)
    (hx : 120 ≤ radiusB x) (p : Covariance.Atom G f)
    (hs : S.patch.Branches S.kernel G) (H : Teams S (Covariance.Terrain.home S p) (peekR S.patch x) (peekD S.patch x) F F' A A' t t' V V')
include hs H
lemma line_zone : linePay T A F t V x hx p L = linePay T A' F' t' V' x hx p L := by
  unfold linePay; congr 1; ext k m
  have hi := aboutWin k.property
  exact seenA T k.val m.val hs (H.zone (k:=lengthA S.patch x) (s:=roundA S.patch x) (by unfold peekR; omega)
      (by unfold peekD; omega))

lemma pair_zone :
    linePay T A F t V x hx p L-linePay T noHole F t 1 x hx p L =
      linePay T A' F' t' V' x hx p L-linePay T noHole F' t' 1 x hx p L := by
  apply congr_arg₂ (· - ·)
  · exact line_zone _ _ _ _ _ _ _ _ _ _ _ _ _ hs H
  have H' : Teams S (Covariance.Terrain.home S p) (peekR S.patch x) (peekD S.patch x) F F' noHole noHole t t' (1:Config G c) 1 :=
    ⟨fun _ _ => rfl,H.tree,fun _ _ => Iff.rfl,fun _ _ => Iff.rfl,fun _ _ => Iff.rfl,H.branch,H.point⟩
  exact line_zone _ _ _ _ _ _ _ _ _ _ _ _ _ hs H'

omit hs H in
theorem nearby_zone
    {e' : Plate G S} (h' : Doors e') (i' : Key e'.forest G)
    (Y' : GaussianScalar.Frozen (held e' A') G) {P : Teller G} (hT : P.Funds S T)
    (hS : Bid.Larger (G:=G) S) (ht : e.tube=T) (ht' : e'.tube=T)
    (hb : 120 ≤ radiusB e.x) (hb' : 120 ≤ radiusB e'.x) (hp : e.x=x) (hp' : e'.x=x)
    (hi : key e i=p) (hi' : key e' i'=p)
    (HH : Teams S (Covariance.Terrain.home S p) (peekR S.patch x) (peekD S.patch x) e.forest e'.forest A A' t t' V V')
    (v : Expense) :
    (page e h A t V).nearby v (frame e hb) e.Flat Y i =
      (page e' h' A' t' V').nearby v (frame e' hb') e'.Flat Y' i' := by
  have hx : 120 ≤ radiusB x := hp ▸ hb
  have hcost (e : Plate G S) (h : Doors e) (ht : e.tube=T) (A t V) (hb : 120 ≤ radiusB e.x) (hp : e.x=x)
      i (hi : key e i=p) Y :
      (page e h A t V).nearby v (frame e hb) e.Flat Y i = -(linePay T A e.forest t V x hx p v.high - linePay T noHole e.forest t 1 x hx p v.high)/2 := by
    have hv : (page e h noHole t 1).sigma 1=e.Flat := by
      have hi := canonical e h t (ht ▸ hT) hS |>.2.2
      rw [hi,sigma_eq,← Native.ground_gram e.tube e.forest t e.x hS.1]; ext i j
      let x (i : Key e.forest G) : Bits G (held e noHole) := (⟨i.1, clear _ _⟩,i.2)
      exact congr_fun (congr_fun (sortBits _ _ 1) (.inl (x i))) (.inl (x j))
    unfold Fiber.nearby
    rw [← hv, local_scan _ _ _ _ Y,local_scan _ _ _ _ (1:_),hi]
    rw [ht]; cases hp; rfl
  rw [hcost _ _ ht _ _ _ hb hp i hi Y,hcost _ _ ht' _ _ _ hb' hp' i' hi' Y', pair_zone _ _ _ _ _ _ _ _ _ _ _ _ _ hS.1 HH]
end compare

open RG.Supply Pressure.Testing
variable {C : Sheet G} {D : Rolls C} {Θ : Protection D} {W : Delays Θ} {Y : Bar W} {I : Wait Y}
    {Z : ChartRatio G} {K : MapPrices} {P : PostCost D} (B : Input.Directed G I Z K P)
    {r : GaussianFieldAlignment.Tickets} {ε g a E : ℕ → ℕ → ℝ} {k : ℕ → ℕ → ℕ} {b : ℕ → ℕ → Covariance.Sale.Tab}


end YM.SectorTools.ActualScalar.Locations
