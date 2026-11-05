import YM.MultiNext.SIGNED_SOURCE_CONTINUATION.Crossing
import YM.Work.F03.Transport

set_option warningAsError false

/-!
# Linear curl estimate on the common Horizon

From fine diagonal inverse and the transport identity, and TRUE cochain
forms; no link component ordering assumed interchangeable without proof.
Ask on the input a patch-ready bound (exp allowed as a function of coarse
distance to THIS point, potentially weaker than a global estimate). Can
apply if the axial/tags path gauges have already supplied it. Does not
claim this price, e.g. beyond a no-hole buffer before exponential
comparison and true B/q cases. -/
set_option autoImplicit false
noncomputable section
namespace YM.MultiNext.SignedSource.Forecast
open Function Filter Finset Lattice Wilson RG Labels Laurent Bloch Exterior Matrix Precision
open  Pattern Newt Next.Free
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {c n : Side} {E m m' : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
  {g : Ratio c n} {G : Gauge} {P : StepData c n} {A V M α γ β : ℝ}

def sheltered (p : Co n m' → E) (v : Site n) (M α : ℝ) := ∀ i, ‖p i‖ ≤ M*Real.exp (α* separation i.1 v)

section
variable {m' : Type*} [Fintype m']
omit [Fintype m] [DecidableEq m] [Fintype m'] in
private lemma check {p : Row m m'} (hp : p.strip β A) (_hA : 0 ≤ A) (_hβ : 0<β) (L : Side) {x : m} {i : m'} (q r : Site L)
    (v : Co L m' → E) (he : sheltered v r V α) (ha : 0 ≤ α) (hV : 0 ≤ V) (hh : α ≤ β) :
    ‖∑' j : Cover,p x i j • v (wrap L j+q,i)‖ ≤ A*V*Real.exp (α*separation q r) := by
  let f (j : Cover) := p x i j
  let b := Real.exp (α*separation q r)
  let a (j : Cover) := Real.exp (β*size j)
  let u j := v (wrap L j+q,i)
  have hf : SumBudget (fun j => a j*‖f j‖) A := hp x i
  let y j := (V*b)*(a j*‖f j‖)
  have hx : Summable y := hf.2.1.mul_left _
  have h j : ‖f j • u j‖ ≤ y j := by
    have hp := he (wrap L j+q,i)
    have ht := separation_triangle (wrap L j+q) q r
    have hu : separation (wrap L j+q) q ≤ size j := by unfold separation; rw [add_sub_cancel_right]; exact Newt.wrapped ..
    have hy : (separation (wrap L j+q) r :ℝ) ≤ ↑(size j)+separation q r := by exact_mod_cast ht.trans (Nat.add_le_add_right hu _)
    have hb : α*separation (wrap L j+q) r ≤ β*size j+α*separation q r := calc
      _ ≤ α*((size j:ℝ)+separation q r) := mul_le_mul_of_nonneg_left hy ha
      _ ≤ _ := by rw [mul_add]; gcongr
    rw [norm_smul]
    apply le_trans (mul_le_mul_of_nonneg_left (hp.trans (mul_le_mul_of_nonneg_left (Real.exp_monotone hb) hV)) (norm_nonneg _))
    unfold y a b; rw [Real.exp_add]; ring_nf; rfl
  have hS := hx.of_nonneg_of_le (fun i => norm_nonneg _) h
  apply (norm_tsum_le_tsum_norm hS).trans ((hS.tsum_le_tsum h hx).trans ?_)
  unfold y; rw [tsum_mul_left]
  refine (mul_le_mul_of_nonneg_left hf.2.2 (mul_nonneg hV (Real.exp_pos _).le)).trans_eq ?_
  ring

omit [Fintype m] [DecidableEq m] in
private lemma pile (P : Row m m') (u : Co n m' → E) (h : P.strip α A) (ht : 0 < α) (b : Co n m) :
    load (P.acts n) u b = ∑ j, ∑' i,P b.2 j i • u (wrap n i+b.1,j) := by
  unfold load; simp only [Row.acts,of_apply]
  rw [Fintype.sum_prod_type,sum_comm]; apply sum_congr rfl; intro j _
  let f := P b.2 j
  let a v i := if v=b.1+wrap n i then f i else 0
  have he : Summable f := (Row.rights α A h ht.le ..).of_norm
  have hA (v : Site n) : Summable (a v) := by
    have hi := he.indicator {i | v=b.1+wrap n i}
    rw [show ({i | v=b.1+wrap n i} : Set Cover).indicator f=a v by funext i; simp [a,Set.indicator]] at hi; exact hi
  change (∑ v : Site n,(∑' i,a v i) • u (v,j)) = _
  simp_rw [← Summable.tsum_smul_const (hA _)]
  rw [← Summable.tsum_finsetSum (f:=fun v i => a v i • u (v,j)) (fun v _ => (hA v).smul_const _)]
  exact tsum_congr fun i => by simp [a,ite_smul,f,add_comm]

omit [Fintype m] [DecidableEq m] in
lemma shelters {p : Row m m'} (hp : p.strip β A) (hA : 0 ≤ A) (hβ : 0<β) (L : Side) (r : Site L)
    (v : Co L m' → E) (he : sheltered v r V α) (ha : 0 ≤ α) (hV : 0 ≤ V) (hh : α ≤ β) :
    sheltered (load (p.acts L) v) r ((Fintype.card m' : ℝ)*A*V) α := by
  intro i; rw [pile p v hp hβ]; apply (norm_sum_le ..).trans
  refine (sum_le_sum (fun j _ => check hp hA hβ L i.1 r v (x:=i.2) (i:=j) he ha hV hh)).trans ?_; simp; ring_nf; rfl

omit [Fintype m] [DecidableEq m] in
lemma flow {p : Cross g.count m m'} (hp : p.strip β A) (hA : 0 ≤ A) (hβ : 0<β) (r : Site n)
    (v : Co c m' → E) (he : sheltered v (g.parent r) V α) (ha : 0 ≤ α) (hV : 0 ≤ V) (hh : α ≤ β) :
    sheltered (load (installed g p) v) r (Real.exp α * Fintype.card m'*A*V) α := by
  have hs := shelters hp hA hβ c (g.parent r) v he ha hV hh
  intro i
  apply (hs (splitCo g m i)).trans
  rw [split_co]; dsimp only
  have hx : separation (g.parent i.1) (g.parent r) ≤ separation i.1 r+1 := by
    apply Nat.le_of_mul_le_mul_left _ g.count.property
    have h := Corona.foreshorten g i.1 r
    rw [mul_add, mul_one]; exact h.trans (Nat.add_le_add_right (le_mul_of_one_le_left (Nat.zero_le _) g.count.property) _)
  have hS : α*separation (g.parent i.1) (g.parent r) ≤ α*separation i.1 r+α := calc
    _ ≤ α*(↑(separation i.1 r)+1) := mul_le_mul_of_nonneg_left (by exact_mod_cast hx) ha
    _ = _ := by ring
  refine (mul_le_mul_of_nonneg_left (Real.exp_monotone hS) (show 0 ≤ (Fintype.card m':ℝ)*A*V by positivity)).trans_eq ?_
  rw [Real.exp_add]; ring
end

lemma comatrix (p : Co n (TypeFace 1) → G.Color) : dColor G n 1 p=load (Exterior.d 1 n) p := by
  unfold Exterior.dColor Exterior.parts load
  funext i; ext j
  simp [mulVec,dotProduct] -- WithLp coe_sum_apply etc

theorem foresail {H H' : Bed} {T : Towers P.patch.L} (h : Towers.Diagonal P H H' T)
    (h' : H.dual_diag.acts n*H.diagonal.acts n=1) (hf : H.dual_diag.strip β M) (hg : H'.diagonal.strip γ A)
    (hT : T.T.strip γ (A/(P.patch.L.val:ℝ)^2)) (hα : 0≤α) (hβ : 0<β) (hγ : 0<γ)
    (ha : α≤β) (hc : α≤γ) (hM : 0≤M) (hA : 0≤A) (p : Co c (TypeFace 1) → G.Color) (r : Site n) (hV : 0≤V)
    (hp : sheltered (load (Exterior.d 1 c) p) (P.ratio.parent r) V α) (a : PlaqAxes) :
    let s : ℝ := Fintype.card (TypeFace 2)
    ‖Work.F03.faceCurl (r,a) (load (installed P.ratio T.A0) p)‖ ≤ (s*M* (Real.exp α*s*A*(s*A*V))) /(P.patch.L.val:ℝ)^2 := by
  intro s; let x := load (Exterior.d 1 c) p; let g := P.ratio; let L : ℝ := (P.patch.L).val
  rw [Work.F03.faceCurl,comatrix]
  have he := h.stays
  have hx : Exterior.d 1 n * installed g T.A0= H.dual_diag.acts n* (installed g T.T * (H'.diagonal.acts c*Exterior.d 1 c)) := by
    unfold g
    rw [← Matrix.mul_assoc (installed P.ratio T.T), he,← Matrix.mul_assoc,← Matrix.mul_assoc,h',Matrix.one_mul]
  let i := plaquette a
  rw [← Newt.load_mul,hx, Newt.load_mul, Newt.load_mul, Newt.load_mul]
  have hi := shelters hg hA hγ c _ x hp hα hV hc
  have hh : (g.count.val:ℝ)=L := rfl
  have hy := flow (p:=T.T) (g:=g) hT (show 0 ≤ A / L^(2:ℕ) by positivity) hγ r _ hi hα (by change 0 ≤ s*A*V; unfold s; positivity) hc
  have hz := shelters hf hM hβ n r _ hy hα (by change 0 ≤ Real.exp α*s*(A/L^2)*(s*A*V);unfold s; positivity) ha (r,i)
  rw [show separation (r,i).1 r=0 from separation_self _,Nat.cast_zero,mul_zero,Real.exp_zero,mul_one] at hz
  apply hz.trans (le_of_eq ?_)
  unfold s; ring
end YM.MultiNext.SignedSource.Forecast
