import YM.Bid.Loan
import YM.Next.BOUNDARY.Parallel

/-!
# Descent on *these* quotient fields (boost, inclusions, J_E)

Real spatial rotations AND reflection supplied from this O(4) Euclidean action.
`conj` commutes with its real lie derivatives; reflection changes the sign on
the time--space planes. Hence `adj`, which is *anti*linear, commutes with the
actual boosts. No claim of bounded action on the algebraic Union in any norm.
This closes a boundary compatibility / spin producer WITHOUT assuming a lift
through a free model. The proof of the Euclidean inputs remains upstream.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.BOUNDARY.Descent
open Function Filter NormedSpace Set Mink Table Boundary Complex
open scoped Topology Matrix.Norms.Frobenius
attribute [local instance] fieldOp_smul fieldOp_top

variable {G : Gauge} {L : Register G} {S : Table L} (R : Rotation S) {P : DiffPlan S} {H : S.RealSpin}

private def realCast (d : ℕ) (Q : S.Field d →ₛₗ[starRingEnd ℂ] S.Field d) : S.Field d →L[ℝ] S.Field d :=
  LinearMap.toContinuousLinearMap {
    toFun := Q, map_add' := map_add Q
    map_smul' := fun c x => by
      change Q (c • x)=c • Q x; simp only [RCLike.real_smul_eq_coe_smul (K := ℂ),map_smulₛₗ]
      exact congr_arg (· • Q x) (Complex.conj_ofReal c) }

lemma lie_real (h : Spin.Port R H) (d : ℕ) (U : Ortho.Skew) (v : S.Field d) :
    S.conj H d (lie R d U v)=lie R d U (S.conj H d v) := by
  have he : HasDerivAt (fun t => S.conj H d (R.act d (Ortho.oneParameter U t) v))
      (S.conj H d (lie R d U v)) 0 :=
    (realCast d (S.conj H d)).hasFDerivAt.comp_hasDerivAt 0 (h.spinAt d U v)
  simp_rw [h.real] at he; exact he.unique (h.spinAt d U _)

lemma er_reflect (h : Spin.Port R H) (d : ℕ) (v : S.Field d) :
    er R d (Signed.reflect timeAxis) v=S.mirror H d (Signed.mirror timeAxis) v :=
  h.signed ..

lemma rank_adj (h : Spin.Port R H) (d : ℕ) (a : SpaceAxis) (v : S.Field d) :
    S.adj H d timeAxis (rankAction R d (B a) v)=rankAction R d (B a) (S.adj H d timeAxis v) := by
  let m := Signed.reflect timeAxis
  have he := er_lie R h d m (Q a)
  have hp : orbitA m (Q a) = -(Q a) := by
    apply Subtype.ext
    change theta*(Q a).val * star theta = -(Q a).val
    rw [← BQ a,star_theta,← mul_assoc theta, time_parity a]
    simp only [neg_mul,mul_assoc, theta_sq, mul_one]
  rw [hp,map_neg] at he
  have hk : S.adj H d timeAxis (lie R d (Q a) v) = -(lie R d (Q a) (S.adj H d timeAxis v)) := by
    unfold Table.adj; simp only [LinearMap.comp_apply, lie_real R h, ← er_reflect R h]
    exact DFunLike.congr_fun he (S.conj H d v)
  simp_rw [rank_B R]
  change S.adj H d timeAxis ((-I) • lie R d (Q a) v) = (-I) • lie R d (Q a) (S.adj H d timeAxis v)
  rw [map_smulₛₗ, hk, show starRingEnd ℂ (-I)=I by simp, smul_neg, neg_smul]

lemma eb_through {d e : ℕ} (a : SpaceAxis) (f : S.Field d →L[ℝ] S.Field e)
    (h : ∀ x, f (rankAction R d (B a) x)=rankAction R e (B a) (f x)) (t : ℝ) (x : S.Field d) :
    f (eb R d a t x) = eb R e a t (f x) := by
  let g t := f (eb R d a t x)
  let k t := eb R e a t (f x)
  let Z := (rankAction R e (B a)).restrictScalars ℝ
  have hg (u) : HasDerivAt g (Z (g u)) u := by
    change HasDerivAt g (rankAction R e (B a) (f _)) u
    rw [← h]; exact f.hasFDerivAt.comp_hasDerivAt u (on_field (eb_left R d a u) x)
  have hk (u) : HasDerivAt k (Z (k u)) u := on_field (eb_left R e a u) (f x)
  have hi : g 0=k 0 := by simp [g,k,eb_zero]
  exact congr_fun (ODE_solution_unique_univ (s := fun _ => Set.univ) (fun (_ : ℝ) => Z.lipschitz.lipschitzOnWith)
    (fun u => ⟨hg u,mem_univ _⟩) (fun u => ⟨hk u,mem_univ _⟩) hi) t

lemma er_adj (h : Spin.Port R H) (d : ℕ) (k : Ortho) (hk : Lorentz.spatialTurn k) (v : S.Field d) :
    S.adj H d timeAxis (er R d k v)=er R d k (S.adj H d timeAxis v) := by
  have hp : S.conj H d (er R d k v)=er R d k (S.conj H d v) := h.real ..
  unfold Table.adj; rw [LinearMap.comp_apply, LinearMap.comp_apply, ← er_reflect R h, ← er_reflect R h,hp]
  change (er R d (Signed.reflect timeAxis)*er R d k) _=(er R d k*er R d (Signed.reflect timeAxis)) _
  rw [← er_mul R h, ← er_mul R h, show Signed.reflect timeAxis*k=k*Signed.reflect timeAxis from
    Subtype.ext (space_parity k hk)]

lemma spins_adj (h : Spin.Port R H) (d : ℕ) (k : Lorentz) (v : S.Field d) :
    S.adj H d timeAxis (spins R d k v)=spins R d k (S.adj H d timeAxis v) := by
  have he (a s x) : S.adj H d timeAxis (eb R d a s x)=eb R d a s (S.adj H d timeAxis x) :=
    eb_through R a (realCast d (S.adj H d timeAxis)) (rank_adj R h d a) s x
  change S.adj H d timeAxis (eb _ _ 0 _ (eb _ _ 1 _ (eb _ _ 2 _ (er R d _ v))))=
    eb _ _ 0 _ (eb _ _ 1 _ (eb _ _ 2 _ (er _ _ _ _)))
  rw [he 0,he 1,he 2,er_adj R h d _ (oriented k)]

lemma rotation_port (h : R.Laws P H) : Spin.Port R H := ⟨h.spin,h.fixes,h.group,h.signed,h.real,h.infinitesimal⟩

lemma rank_through (h : R.Laws P H) {d e : ℕ} (hp : d≤e) (a : SpaceAxis) (v : S.Field d) :
    P.rise hp (rankAction R d (B a) v)=rankAction R e (B a) (P.rise hp v) := by
  let T := ((P.rise hp).toContinuousLinearMap).restrictScalars ℝ
  have hn : HasDerivAt (fun t => P.rise hp (R.act d (Ortho.oneParameter (Q a) t) v))
      (P.rise hp (lie R d (Q a) v)) 0 :=
    T.hasFDerivAt.comp_hasDerivAt 0 (h.infinitesimal d _ v)
  have ht := h.infinitesimal e (Q a) (P.rise hp v)
  simp_rw [h.filtered] at ht
  rw [rank_B,rank_B]; change P.rise hp ((-I) • _) = (-I) • _
  rw [map_smul]; exact congr_arg _ (hn.unique ht)

lemma spins_through (h : R.Laws P H) {d e : ℕ} (hp : d≤e) (k : Lorentz) (v : S.Field d) :
    P.rise hp (spins R d k v)=spins R e k (P.rise hp v) := by
  have he (a s x) : P.rise hp (eb R d a s x)=eb R e a s (P.rise hp x) :=
    eb_through R a ((P.rise hp).toContinuousLinearMap.restrictScalars ℝ) (rank_through R h hp a) s x
  change P.rise hp (eb _ _ 0 _ (eb _ _ 1 _ (eb _ _ 2 _ (er R d _ v))))=
    eb _ _ 0 _ (eb _ _ 1 _ (eb _ _ 2 _ (er _ _ _ _)))
  rw [he 0,he 1,he 2, show P.rise hp (er R d (orientation k) v) = er R e (orientation k) (P.rise hp v) from
    (h.filtered _ _ hp _ _).symm]

lemma spatial_spins (h : Spin.Port R H) (d : ℕ) (k : Ortho) (hk : Lorentz.spatialTurn k) :
    spins R d (Lorentz.room k hk) = er R d k := by
  have ht := spatial_right R d h 1 k hk; rwa [one_mul, spins_one R d h, one_mul] at ht

lemma boost_spins (h : Spin.Port R H) (d : ℕ) (a : SpaceAxis) (s : ℝ) :
    spins R d (boost a s)=eb R d a s := by
  have ht := boost_right R d h 1 a s; rwa [one_mul, spins_one R d h, one_mul] at ht

def shell (h : Spin.Port R H) (d : ℕ) (g : Lorentz) : S.Field d ≃ₗ[ℂ] S.Field d := {
  toLinearMap := (spins R d g).toLinearMap
  invFun := spins R d g⁻¹
  left_inv x := by
    change (spins R d g⁻¹*spins R d g) x=x; rw [← spins_mul R d h, inv_mul_cancel, spins_one R d h]; rfl
  right_inv x := by
    change (spins R d g*spins R d g⁻¹) x=x; rw [← spins_mul R d h, mul_inv_cancel, spins_one R d h]; rfl }



/-- The lift doesn't identify S with any other table, nor assume topology on Union. -/
theorem produce (h : R.Laws P H) (hp : S.Symmetric) (ht : P.Inclusions S) : ∃ K : Spins S, K.Descends R H := by
  have hz := rotation_port R h
  have he (g : Lorentz) : ∃ W : S.Union→ₗ[ℂ] S.Union, ∀ d x, W (S.pin d x)=S.pin d (spins R d g x) :=
    (P.uniqueLift hp ht (fun d => (S.pin d).comp (spins R d g).toLinearMap) (by
      intro d e w x; change S.pin e (spins R e g (P.rise w x))=S.pin d (spins R d g x)
      rw [← spins_through R h, P.stays hp ht])).exists
  choose W hW using he
  have h1 (x : S.Union) : W 1 x=x := by
    obtain ⟨d,v,rfl⟩ := P.covered hp ht x; rw [hW,spins_one R d hz]; rfl
  have hmul (f g : Lorentz) (x : S.Union) : W (f*g) x=W f (W g x) := by
    obtain ⟨d,v,rfl⟩ := P.covered hp ht x; rw [hW,hW,hW,spins_mul R d hz]; rfl
  let K : Spins S := {
    shell := shell R hz
    rail g := {
      toLinearMap := W g, invFun := W g⁻¹
      left_inv x := by change W g⁻¹ (W g x)=_; rw [← hmul,inv_mul_cancel,h1]
      right_inv x := by change W g (W g⁻¹ x)=_; rw [← hmul,mul_inv_cancel,h1] } }
  refine ⟨K,hW,h1,hmul, ?_, ?_, ?_, fun g d x => spins_adj R hz d g x⟩
  · intro d v
    exact ((ContinuousLinearMap.apply ℂ (S.Field d) v).continuous.comp (spins_continuous R d hz))
  · intro d a x
    change HasDerivAt (fun t => spins R d (boost a t) x) _ _
    simp_rw [boost_spins R hz]
    have hr := on_field (eb_right R d a 0) x
    rw [eb_zero,one_mul,rank_B] at hr
    exact hr
  intro k hh d x; rw [show K.shell d (Lorentz.room k hh) x=spins R d _ x from rfl, spatial_spins R hz]; rfl

private lemma shell_rep (K : Spins S) (h : K.Descends R H) (d : ℕ) (g k : Lorentz) (v : S.Field d) :
    K.shell d (g*k) v=K.shell d g (K.shell d k v) := by
  apply S.pin_inj; rw [← h.ties,← h.ties,← h.ties,h.representation]

lemma matches_shell (K : Spins S) (h : K.Descends R H) (d : ℕ) (g : Lorentz) (v : S.Field d) :
    K.shell d g v=spins R d g v := by
  have hb (a t x) : K.shell d (boost a t) x=eb R d a t x := by
    let k (s) := (K.shell d (boost a s)).toContinuousLinearEquiv.toContinuousLinearMap
    have h0 : k 0=1 := by
      ext v; apply S.pin_inj; change S.pin d (K.shell d _ v)=S.pin d v
      rw [← h.ties,boost, Ray.boost_start,h.identity]
    have he (t r) : k (t+r)=k t*k r := by
      ext v; change K.shell d (boost a (t+r)) v = _
      rw [boost,Ray.boost_add]; exact shell_rep R K h _ _ _ v
    have hk (v) : HasDerivAt (fun t => k t v) (rankAction R d (B a) v) 0 := by rw [rank_B]; exact h.boosts ..
    exact DFunLike.congr_fun (one_parameter_field h0 he hk t) x
  conv_lhs => rw [← factors g]
  rw [shell_rep R K h,shell_rep R K h,shell_rep R K h, hb,hb,hb,h.spatial]; rfl

end YM.Next.BOUNDARY.Descent

namespace YM.Next.BOUNDARY
open Function Table Boundary
variable {G : Gauge} {L : Register G} {S : Table L} {R : Rotation S} {P : DiffPlan S} {H : S.RealSpin}

/-- Producer of the K seam, also for e.g. a free-table consumer. No Maxwell or
UV stress witness is input. This doesn't construct the Euclidean rotation.
Uniqueness on the ACTUAL proper orthochronous group. -/
theorem spins_producer (hp : S.Symmetric) (ht : P.Inclusions S) (h : R.Laws P H) :
    ∃! K : Spins S, K.Descends R H := by
  obtain ⟨K,hK⟩ := Descent.produce R h hp ht
  refine ⟨K,hK,?_⟩
  intro X hx
  have he : X.shell=K.shell := by
    funext d k; ext x
    exact (Descent.matches_shell R X hx _ _ _).trans (Descent.matches_shell R K hK _ _ _).symm
  have hr : X.rail=K.rail := by
    funext k; ext1 x
    obtain ⟨d,v,rfl⟩ := P.covered hp ht x
    rw [hx.ties,hK.ties,he]
  cases X; cases K; congr

end YM.Next.BOUNDARY
