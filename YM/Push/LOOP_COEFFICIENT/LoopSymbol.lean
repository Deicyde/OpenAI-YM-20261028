import YM.Push.LOOP_COEFFICIENT.DriftKernels
import YM.Push.LOOP_COEFFICIENT.LoopReal
import YM.Push.LOOP_COEFFICIENT.ReadJets


/-! # Exact physical path-array Hessian versus analytic loop symbol -/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops
open Matrix Function Filter Set Lattice RG Wilson Precision Exterior Laurent Bloch Complex
open scoped Topology BigOperators ContDiff
variable {G : Gauge} {n : Side} {p : Momentum} {k : Site n} {W : PathData G} {σ C Λ : ℝ}

def curlSymbol (G : Gauge) (p : Momentum) : Matrix (Sides G) (Axes G) ℂ := of fun i j =>
    if i.2=j.2 then symbol 1 p (plaquette i.1) (coord j.1) else 0

def rawSymbol (G : Gauge) (M : Row (Sides G) (Sides G)) (p : Momentum) :=
    (curlSymbol G (-p)).transpose * (M.read p + (M.read (-p)).transpose) * curlSymbol G p

def orient (G : Gauge) (M : Momentum → Matrix (Axes G) (Axes G) ℂ) (s : Signed) (p : Momentum) :=
    (orbitSymbol G s (-p)).transpose * M (s⁻¹.act p) * orbitSymbol G s p

def loopSymbol (W : PathData G) (p : Momentum) := (Fintype.card Signed:ℂ)⁻¹ • ∑ s : Signed,orient G (rawSymbol G (loopRow W)) s p

lemma curl_entry (x y) : curlColored G n x y = if x.2=y.2 then d 1 n (x.1.1,plaquette x.1.2) (y.1.1, coord y.1.2) else 0 := by
  have he := curl_apply (Pi.single y (1:ℝ)) x.1 x.2
  rw [Matrix.mulVec_single_one, Matrix.col_apply] at he; rw [he]
  change (d 1 n *ᵥ parts G 1 _ _) _ = _; rw [← layer_eq,mulVec,dotProduct,Fintype.sum_prod_type]; conv_lhs => arg 2; ext; rw [← Equiv.sum_comp axisEquiv]
  simp only [coord_map,layer_coord,Pi.single_apply,Prod.ext_iff,mul_ite,ite_and,mul_one,mul_zero]; split <;> simp_all
lemma curl_routed (hp : Matches p k) : Routed (faceGrid G n) (linksGrid G n) k k (cmat (curlColored G n)) (curlSymbol G p) := by
  have he : Routed (Equiv.refl _) (Equiv.refl _) k k (cmat (d 1 n)) (symbol 1 p) := reading p 1 ▸ acts_routed _ (cobound_safe 1) hp
  ext ⟨⟨x,i⟩,a⟩ ⟨j,b⟩
  have h := congr_fun (congr_fun he (x,plaquette i)) (coord j)
  rw [plane_mul] at h ⊢; simp only [Matrix.mul_apply,Fintype.sum_prod_type] at h ⊢
  conv at h => lhs; arg 2; ext; rw [← Equiv.sum_comp axisEquiv]
  by_cases ha : a=b <;> simp_all [cmat_apply,approached,curl_entry,curlSymbol,coord_map,coord_iff,plane,mul_ite,ite_and,faceGrid,linksGrid]
lemma faces_routed (hp : Matches p k) (h : Row.safe (loopRow W)) : Routed (faceGrid G n) (faceGrid G n) k k (cmat (loopFaces W n)) ((loopRow W).read p) := by
  ext i j; have he := congr_fun (congr_fun (acts_routed _ h hp) (faceGrid G n i)) j
  simp only [plane_mul,Equiv.refl_apply] at he ⊢
  rw [← he,Matrix.mul_apply,Matrix.mul_apply]; conv_rhs => rw [← Equiv.sum_comp (faceGrid G n)];
  rfl

lemma transpose_same {a b m l : Type} [Fintype a] [Fintype b] [Fintype m] [Fintype l] [DecidableEq m] [DecidableEq a] [DecidableEq b]
    {A : Grid n l a} {B : Grid n m b} {X : Matrix l m ℂ} {V : Momentum → Matrix a b ℂ}
    (h : ∀ p i, Matches p i → Routed A B i i X (V p)) (hp : Matches p k) : Routed B A k k X.transpose (V (-p)).transpose := by
  simpa only [add_zero] using! (Synced.routed_transpose (p:=0) (k:=k) (M:=A) (N:=B) (fun k => ⟨_,by rw [add_zero]; exact h _ _ (mon_matches k)⟩) (by simpa only [add_zero] using h _ _ hp.neg))

lemma raw_routed (h : Row.safe (loopRow W)) (hp : Matches p k) : Routed (linksGrid G n) (linksGrid G n) k k (cmat (rawLoop W n)) (rawSymbol G (loopRow W) p) := by
  simp only [rawLoop,cmat_mul,map_add]; exact ((transpose_same (fun _ _ => curl_routed) hp).mul ((faces_routed hp h).add (transpose_same (fun _ _ hp => faces_routed hp h) hp))).mul (curl_routed hp)

lemma loopPrice_sample (h : Row.safe (loopRow W)) (hp : Matches p k) (i : Site n) : sample (linksGrid G n) (linksGrid G n) (cmat (loopPrice W n)) i k = if i+k=0 then loopSymbol W p else 0 := by
  have hh : Compares (linksGrid G n) (linksGrid G n) (cmat (rawLoop W n)) _ 0 := Compares.of_routed (fun _ _ hp => raw_routed h hp)
  let S (s : Signed) := cmat ((linkSpin s (1:Config G n)).transpose * rawLoop W n * linkSpin s 1)
  have he s : sample (linksGrid G n) (linksGrid G n) (S s) i k = if i+k = 0 then orient G (rawSymbol G (loopRow W)) s p else 0 := by
    simp only [S,cmat_mul,show cmat (linkSpin s (1:Config G n)).transpose = (cmat (linkSpin s (1:Config G n))).transpose from rfl]; split
    next hi => rw [eq_neg_of_add_eq_zero_left hi,sample_sandwich (cmat (rawLoop W n)) (orbit_routed hp.neg s) (orbit_routed hp s), Signed.act_neg, hh.exact_sample (hp.signed s⁻¹)]; rfl
    next hi => rw [sample_sandwich (cmat (rawLoop W n)) (orbit_routed (mon_matches i) s) (orbit_routed hp s),hh.off _ _ (by rw [← Signed.act_add,← s⁻¹.act_zero]; exact fun h => hi (s⁻¹.act_injective h)),Matrix.mul_zero,Matrix.zero_mul]
  have hv : cmat (loopPrice W n) = (Fintype.card Signed:ℂ)⁻¹ • ∑ s,S s := by
    rw [loopPrice,map_smul,map_sum,← IsScalarTower.algebraMap_smul ℂ]; simp [S]
  rw [hv, sample_smul,sample,Matrix.mul_sum,Matrix.sum_mul,Finset.smul_sum]; change _ • ∑ s, sample _ _ (S s) i k = _; simp_rw [he]; split <;> simp [*,loopSymbol]

lemma loop_compares (h : Row.safe (loopRow W)) : Compares (linksGrid G n) (linksGrid G n) (cmat (loopPrice W n)) (loopSymbol W) 0 := ⟨fun i k hi => by rw [loopPrice_sample h (mon_matches k),if_neg hi],fun hp i j => by simp [loopPrice_sample h hp]⟩

lemma signed_tube (s : Signed) (h : p∈Tube σ) : s.act p∈Tube σ := by intro i; unfold Signed.act; split <;> simpa using h _
lemma signed_period (s : Signed) (z : Cover) : s.act (Laurent.reciprocal z) = reciprocal (s.act z) := by ext1; unfold Signed.act reciprocal; split <;> simp [*]
lemma symbol_period (p : Momentum) (z : Cover) (r : ℕ) : symbol r (p+reciprocal z)=symbol r p := by rw [← reading,Row.periods,reading]
lemma corner_period (s : Signed) (p : Momentum) (z : Cover) (i : Axis) : corner s (p+reciprocal z) i = corner s p i := by simp only [corner,← factor,mode_phase,mode_periodic,mul_one]
lemma orbit_period (s : Signed) (p : Momentum) (z : Cover) : orbitSymbol G s (p+reciprocal z) = orbitSymbol G s p := by simp only [orbitSymbol,corner_period]
lemma curl_period (p : Momentum) (z : Cover) : curlSymbol G (p+reciprocal z) = curlSymbol G p := by simp only [curlSymbol,symbol_period]
lemma raw_period (M : Row (Sides G) (Sides G)) (p : Momentum) (z : Cover) : rawSymbol G M (p+reciprocal z) = rawSymbol G M p := by simp only [rawSymbol,neg_add,curl_period,← reciprocal_neg,Row.periods]
lemma loop_period (W : PathData G) (p : Momentum) (z : Cover) : loopSymbol W (p+reciprocal z) = loopSymbol W p := by simp only [loopSymbol,orient,neg_add,← reciprocal_neg,Signed.act_add,signed_period,raw_period,orbit_period]

open scoped Matrix.Norms.L2Operator
lemma orbit_diff (s : Signed) : ContDiffAt ℂ ω (orbitSymbol G s) p := analyticMatrix fun i j => by unfold orbitSymbol; dsimp only [of_apply]; split <;> first | exact (corner_diff ..).contDiffAt | exact contDiffAt_const
lemma curl_diff : ContDiffAt ℂ ω (curlSymbol G) p := analyticMatrix (fun i j => by unfold curlSymbol; dsimp only [of_apply]; split <;> first | exact analyticComponent symbol_diff .. | exact contDiffAt_const)
lemma raw_diff {M : Row (Sides G) (Sides G)} (hs : 0<σ) (h : M.strip σ C) (hp : p∈Tube (σ/2)) : ContDiffAt ℂ ω (rawSymbol G M) p :=
  analyticMul (analyticMul (analyticTranspose (curl_diff.comp (f:=(-·)) p (by fun_prop))) ((row_analytic h hs hp).add (analyticTranspose ((row_analytic h hs (tube_neg hp)).comp (f:=(-·)) p (by fun_prop))))) curl_diff
lemma orient_diff {M : Momentum → Matrix (Axes G) (Axes G) ℂ} (s : Signed) (h : ContDiffAt ℂ ω M (s⁻¹.act p)) : ContDiffAt ℂ ω (orient G M s) p :=
  analyticMul (analyticMul (analyticTranspose ((orbit_diff s).comp (f:=(-·)) p (by fun_prop))) (h.comp p (sign_diff s⁻¹).contDiffAt)) (orbit_diff s)
lemma loop_diffAt (hs : 0<σ) (h : (loopRow W).strip σ C) (hp : p∈Tube (σ/2)) : ContDiffAt ℂ ω (loopSymbol W) p :=
  (ContDiffAt.sum (f:=orient G (rawSymbol G (loopRow W))) (fun i _ => orient_diff _ (raw_diff hs h (signed_tube i⁻¹ hp)))).const_smul _
lemma raw_four {q} (h : W.Bounds q σ C Λ) (p : Momentum) : UnderMatrix (rawSymbol G (loopRow W)) p 4 := by
  have hr := row_analytic (loopRow_budget h.width h.two) h.width (z:=0) (Work.F07.realStrip _ (half_pos h.width) (star_zero (R:=Momentum)))
  have hc (p : Momentum) := UnderMatrix.one (p:=p) (show curlSymbol G 0 = 0 by ext i j; simp [curlSymbol, symbol,wedge,Exterior.q])
  have ha := analyticTranspose (curl_diff (G:=G).comp (f:=(-·)) 0 (by fun_prop))
  have hb := analyticTranspose ((show ContDiffAt ℂ ω (loopRow W).read (-0) by simpa using hr).comp (f:=(-·)) 0 (by fun_prop))
  have hx := under_loopRow h
  exact UnderMatrix.mul (analyticMul ha (hr.add hb)) curl_diff ((under_negate (hc (-p))).mul ha (hr.add hb) ((hx p).add hr hb (under_negate (hx (-p))))) (hc p)
lemma orient_four {M : Momentum → Matrix (Axes G) (Axes G) ℂ} (hm : ContDiffAt ℂ ω M 0) (h : ∀ p, UnderMatrix M p 4) (s : Signed) (p : Momentum) : UnderMatrix (orient G M s) p 4 := by
  have he := analyticTranspose ((orbit_diff (G:=G) s).comp (f:=(-·)) 0 (by fun_prop)); have hm := (show ContDiffAt ℂ ω M (s⁻¹.act 0) by simpa using hm).comp 0 (sign_diff s⁻¹).contDiffAt
  have hh : UnderMatrix (M ∘ s⁻¹.act) p 4 := fun i j k hk => (by simpa only [Function.comp_apply,lineD,act_smul] using! h (s⁻¹.act p) i j k hk)
  exact (((UnderMatrix.zero _ p).mul he hm hh).mul (analyticMul he hm) (orbit_diff s) (UnderMatrix.zero _ p))
lemma loop_four {q} (h : W.Bounds q σ C Λ) (p : Momentum) : UnderMatrix (loopSymbol W) p 4 := by
  intro i j k hk; have hs := raw_diff h.width (loopRow_budget h.width h.two) (Work.F07.realStrip _ (half_pos h.width) (star_zero (R:=Momentum)))
  have hd s := analyticComponent (orient_diff s (by rw [Signed.act_zero]; exact hs)) i j
  simp only [loopSymbol,Matrix.smul_apply,smul_eq_mul,Matrix.sum_apply,line_const_mul,line_sum _ _ (fun s _ => hd s),fun s => orient_four hs (raw_four h) s p i j k hk,Finset.sum_const_zero,mul_zero]
end YM.Push.Loops
