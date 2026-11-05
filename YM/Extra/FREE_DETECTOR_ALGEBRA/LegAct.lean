import YM.Extra.FREE_DETECTOR_ALGEBRA.Covariance
import YM.Extra.FREE_DETECTOR_ALGEBRA.Kelvin

set_option warningAsError false

/-!
# Covariance of the one-leg Gram

Will give symmetry of the reflected real Gram. The Wick extension uses
its complex extension (complex conjugation on the reflected side only).
-/
set_option autoImplicit false
noncomputable section
namespace YM.Extra.FD
open Function Set Filter Tensor Analysis Maxwell
open scoped Topology ContDiff BigOperators RealInnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] {j : ℕ}

section ortho
variable [InnerProductSpace ℝ F]
section
variable {V : Type*} [AddCommGroup V] [Module ℝ V]

lemma mono_pull_dot (s : Ortho) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v w : Axis → V) :
    ∑ a : Axis, B (monoForm s.val v a) (w a) = ∑ a : Axis, B (v a) (monoForm s⁻¹.val w a) := by
  simp only [mono_eval,_root_.map_sum,_root_.map_smul, LinearMap.sum_apply, LinearMap.smul_apply, inv_at]
  rw [Finset.sum_comm]

lemma mono_dot (s : Ortho) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v w : Axis → V) :
    ∑ a : Axis, B (monoForm s.val v a) (monoForm s.val w a) = ∑ a : Axis, B (v a) (w a) := by
  rw [mono_pull_dot,← mono_mul,show (s⁻¹.val * s.val : M4) = 1 from congr_arg Subtype.val (inv_mul_cancel s),mono_one]

lemma bi_pull_dot (s : Ortho) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v w : Rank2 V) :
    ∑ a : Axis, ∑ b : Axis, B (bi s.val v a b) (w a b) = ∑ a : Axis, ∑ b : Axis, B (v a b) (bi s⁻¹.val w a b) := by
  simp only [bi_eval,_root_.map_sum,_root_.map_smul, LinearMap.sum_apply, LinearMap.smul_apply, inv_at]
  let f (a b i j : Axis) := s.val a i • s.val b j • B (v i j) (w a b)
  have e : ∑ a : Axis, ∑ b : Axis, ∑ i : Axis, ∑ j : Axis, f a b i j = ∑ i : Axis, ∑ j : Axis, ∑ a : Axis, ∑ b : Axis, f a b i j := by
    rw [show (∑ a : Axis, ∑ b : Axis, ∑ i : Axis, ∑ j : Axis, f a b i j) =
      (∑ p : Axis × Axis, ∑ q : Axis × Axis, f p.1 p.2 q.1 q.2) by simp_rw [Fintype.sum_prod_type]]
    rw [Finset.sum_comm]; simp_rw [Fintype.sum_prod_type]
  exact e

lemma bi_dot (s : Ortho) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (v w : Rank2 V) :
    ∑ a : Axis, ∑ b : Axis, B (bi s.val v a b) (bi s.val w a b) = ∑ a : Axis, ∑ b : Axis, B (v a b) (w a b) := by
  rw [bi_pull_dot,← bi_mul,show (s⁻¹.val * s.val : M4) = 1 from congr_arg Subtype.val (inv_mul_cancel s),bi_one]
end

lemma byDir_dot (s : Ortho) (P Q : T E4 F j) : dotDir (byDir s P) (byDir s Q) = dotDir P Q := by
  induction j with
  | zero =>
    have he (P : T E4 F 0) : byDir s P = P := by
      ext1 v; exact congr_arg P (Subsingleton.elim ..)
    rw [he,he]
  | succ j ih =>
    let C (P : T E4 F (j+1)) (i : Axis) := P.curryLeft (basis i)
    have he (P : T E4 F (j+1)) (i : Axis) : C (byDir s P) i = monoForm s.val (fun a => byDir s (C P a)) i := by
      have he := mov_inv_decomp s i
      change _ = ∑ a : Axis, s.val i a • byDir s (C P a)
      rw [show (∑ a : Axis, s.val i a • byDir s (C P a)) = byDir s (P.curryLeft (mov s⁻¹ (basis i))) by
        rw [he,_root_.map_sum,_root_.map_sum]; simp_rw [_root_.map_smul]; rfl]
      ext1 v
      apply congr_arg P
      ext1 k; refine Fin.cases ?_ (fun _ => ?_) k <;> rfl
    have hd (P Q : T E4 F (j+1)) : dotDir P Q = ∑ i : Axis, dotDir (C P i) (C Q i) := by
      rw [dotDir_eval,sum_dirs]; simp_rw [dir_cons, dotDir_eval]; rfl
    rw [hd, hd]
    simp_rw [he]; rw [mono_dot]; simp_rw [ih]

lemma carry_dot (s : Ortho) (P Q : TwoJet F j) : dotF (carry s P) (carry s Q) = dotF P Q := by
  rw [dotF_eval,dotF_eval]
  change (∑ a : Axis, ∑ b : Axis, dotDir (bi s.val (fun i m => byDir s (P i m)) a b) (bi s.val (fun i m => byDir s (Q i m)) a b)) = _
  rw [bi_dot]; simp_rw [byDir_dot]
end ortho

section
variable [NormedSpace ℝ F]

/-- Compose any tensor coefficient with a motion (germ convention). -/
lemma coeff_mov (s : Ortho) (f : E4 → F) (x : E4) : coeff (f ∘ mov s⁻¹) j x = byDir s (coeff f j (mov s⁻¹ x)) := by
  let L : E4 ≃L[ℝ] E4 := (Ortho.motion s⁻¹).toContinuousLinearEquiv
  have h := L.iteratedFDerivWithin_comp_right f (s := univ) uniqueDiffOn_univ (x := x) (mem_univ (L x)) j
  simp only [preimage_univ,iteratedFDerivWithin_univ] at h
  unfold coeff; rw [_root_.map_smul]
  exact congr_arg (fun V : T E4 F j => ((Nat.factorial j:ℝ))⁻¹ • V) h

lemma coeffFsum {ι : Type*} (j : ℕ) (x : E4) (f : ι → E4 → F) (s : Finset ι)
    (he : ∀ i ∈ s, ContDiffAt ℝ j (f i) x) : coeff (fun y => ∑ i ∈ s, f i y) j x = ∑ i ∈ s, coeff (f i) j x := by
  rw [← coeff_sum j x f s he,funext (fun y => (Finset.sum_apply y s f).symm)]

theorem nth_reel (s : Ortho) {f : Maxwell.Field F} {x : E4} (j : ℕ) (he : ∀ i m, ContDiffAt ℝ j (f i m) (mov s⁻¹ x)) :
    WaveOn.nth (reel s f) j x = carry s (WaveOn.nth f j (mov s⁻¹ x)) := by
  ext1 i; ext1 m
  let T (a b : Axis) := fun y => s.val i a • s.val m b • f a b (mov s⁻¹ y)
  have hd a b : ContDiffAt ℝ j (f a b ∘ mov s⁻¹) x := (he a b).comp x (mov s⁻¹).contDiff.contDiffAt
  have ht a b : ContDiffAt ℝ j (T a b) x := contDiffAt_const.smul (contDiffAt_const.smul (hd a b))
  change coeff (fun y => ∑ a : Axis, ∑ b : Axis, T a b y) j x = ∑ a : Axis, ∑ b : Axis,
    s.val i a • s.val m b • byDir s (coeff (f a b) j (mov s⁻¹ x))
  rw [coeffFsum _ _ _ _ (fun a _ => ContDiffAt.sum fun b _ => ht a b)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [coeffFsum _ _ _ _ (fun b _ => ht a b)]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← coeff_mov]; change coeff (s.val i a • (s.val m b • (f a b ∘ mov s⁻¹))) j x = _
  rw [coeff_smul _ (show ContDiffAt ℝ j (s.val m b • (f a b ∘ mov s⁻¹)) x from contDiffAt_const.smul (hd a b)),
    coeff_smul _ (hd a b)]
end

variable {G : Gauge} {x : E4}

abbrev inversePoint (x : E4) : E4 := rr x • x

theorem reply_radial (P : Sol G.Color j) (hx : x ∈ away) :
    (fun i m => reply (G:=G) P i m x) = (strength j * rr x ^ 2) • bi (face x).val (fun a b => P.field a b (inversePoint x)) := by
  have hv := fun a b : Axis => homogeneous (P.val a b) x (rr x)
  let Q := fun a b : Axis => P.field a b x
  have ht : (fun a b => P.field a b (inversePoint x)) = rr x ^ j • Q := by funext a b; exact hv a b
  have ha (i m) : bi (face x).val Q i m = reflectedF P i m x := anti_face Q (fun a b => P.wave.form a b x (mem_univ _)) x i m
  rw [ht,_root_.map_smul]
  ext1 i; ext1 m
  rw [reply_kelvin P hx]
  simp only [Pi.smul_apply,ha,smul_smul]
  rw [pow_add]; module

lemma mov_away (s : Ortho) (hx : x ∈ away) : mov s x ∈ away := by
  intro he
  exact hx (Ortho.move_injective s ((show mov s x = 0 from he).trans (mov s).map_zero.symm))

theorem radial_move (s : Ortho) (P : Sol G.Color j) (hx : x ∈ away) :
    (fun i m => reply (G:=G) (solO s P) i m x) = bi s.val (fun i m => reply (G:=G) P i m (mov s⁻¹ x)) := by
  rw [reply_radial _ hx,reply_radial _ (mov_away s⁻¹ hx),_root_.map_smul]
  let V (i m : Axis) := P.field i m (inversePoint (mov s⁻¹ x))
  have ht : (fun a b => Sol.field (solO s P) a b (inversePoint x)) = bi s.val V := by
    ext1 i; ext1 m; rw [field_solO,reel]
    have he : mov s⁻¹ (inversePoint x) = inversePoint (mov s⁻¹ x) := by
      dsimp only [inversePoint]; rw [_root_.map_smul,mov_apply,rr_move]
    rw [he]
  have he : (face x).val * s.val = s.val * (face (mov s⁻¹ x)).val := by
    have hh := face_rotate s (mov s⁻¹ x)
    simp only [mov_apply,Ortho.move_inv] at hh
    exact congr_arg Subtype.val hh
  rw [ht,← bi_mul, ← bi_mul,he,mov_apply,rr_move]; rfl

lemma dot_pair (s : Ortho) (P : Sol G.Color j) (hx : x ∈ away) (m : ℕ) :
    WaveOn.nth (reply (G:=G) (solO s P)) m (mov s x) = carry s (WaveOn.nth (reply (G:=G) P) m x) := by
  let y := mov s x
  have hg : mov s⁻¹ y = x := Ortho.inv_move s x
  have he (a b) : reply (G:=G) (solO s P) a b =ᶠ[𝓝 y] reel s (reply (G:=G) P) a b := by
    filter_upwards [open_away.mem_nhds (mov_away s hx)] with t ht
    exact congr_fun (congr_fun (radial_move s P ht) a) b
  have hh : WaveOn.nth (reply (G:=G) (solO s P)) m y = WaveOn.nth (reel s (reply (G:=G) P)) m y := by
    funext i b; exact GermCoeff m (he i b)
  have hd i b : ContDiffAt ℝ m (reply (G:=G) P i b) (mov s⁻¹ y) := by
    rw [hg]; exact ((replied P).smooth i b x hx).of_le (WithTop.coe_le_coe.mpr le_top)
  exact hh.trans (by rw [nth_reel _ _ hd,hg])

theorem leg_cov {l : ℕ} (s : Ortho) (P : Sol G.Color j) (Q : Sol G.Color l) (hx : x ∈ away) :
    legKernel (G:=G) (dualSol _ _ (solO s P)) (dualSol _ _ (solO s Q)) (mov s x) =
    legKernel (G:=G) (dualSol G.Color _ P) (dualSol _ _ Q) x := by
  rw [replyTest _ _ (mov_away s hx),replyTest _ _ hx, dot_pair s P hx]
  rw [show (solO s Q).val=carry s Q.val from rfl,carry_dot]
end YM.Extra.FD
