import YM.Push.STRESS_FLUX.Solve

set_option autoImplicit false
noncomputable section
namespace YM.StressFlux.Annular
open Matching Table Work.A01 Analysis Function Filter Set MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius
variable {G : Gauge} {L : Register G} {S : Table L} {i d D n : ℕ} {V : E4 → E4} {W : DiffPlan S} {H : S.RealSpin}
  {x : Points (n+1)} {χ : E4 → ℝ}

def middle (p : S.Tag) (q : Fin n → S.Tag) (d : ℕ) (z : Points (n+2)) :=
  Ward.here (Fin.cons p (Fin.cons (α:=fun _ => S.Tag) ⟨d,0⟩ q)) z (0 : Fin (n+1)).succ d

lemma middle_eval (p : S.Tag) (q : Fin n → S.Tag) (B : S.Field d) (z : Points (n+2)) :
    middle p q d z B = S.useAt S z (Fin.cons p (Fin.cons ⟨d,B⟩ q)) := by
  unfold middle
  rw [Ward.takes]
  unfold Ward.disc; congr! 1
  funext i
  refine Fin.cases ?_ (fun j => Fin.cases ?_ (fun t => ?_) j) i
  · simp
  · simp
  rw [update_of_ne (Fin.succ_injective _ |>.ne (Fin.succ_ne_zero t))]; rfl

def shellTerm (J : S.Stress) (x : Points (n+1)) (q : Fin n → S.Tag) (χ : E4 → ℝ) (a b : Axis) (y : E4) (d : ℕ) (V : E4 → E4) : S.Field d →ₗ[ℂ] ℂ :=
  Work.A05.weight χ a (fun y => V (y-x 0) b) y • middle ⟨4,J a b⟩ q d (Points.cons y x)

lemma shellTerm_eval (J : S.Stress) (x : Points (n+1)) (q : Fin n → S.Tag) (χ : E4 → ℝ) (a b : Axis) (y : E4) (B : S.Field d) :
    shellTerm J x q χ a b y d V B = term J χ (fun y => V (y-x 0)) x q B a b y := by rw [shellTerm,LinearMap.smul_apply,middle_eval]; rfl

def shellMap (hs : S.Smooth) (J : S.Stress) (q : Fin n → S.Tag) (d : ℕ) (hx : x∈conf _) (hw : Window x χ)
    (hv : ∀ b : Axis, Continuous (fun y => V y b)) : S.Field d →ₗ[ℂ] ℂ where
  toFun := about J χ V x q
  map_add' p t := by
    have ht a b (v : S.Field d) := term_integrable J χ (fun y => V (y-x 0)) x q v hs hx hw a b ((hv b).comp (continuous_id.sub continuous_const))
    simp_rw [about, flux, ← shellTerm_eval, map_add, shellTerm_eval, integral_add (ht _ _ p) (ht _ _ t), Finset.sum_add_distrib]; abel
  map_smul' c p := by simp only [about,flux, ← shellTerm_eval, map_smul, integral_smul, smul_neg, Finset.smul_sum,RingHom.id_apply]

lemma linear (hs : S.Hierarchy) (hd : W.Derivatives S) {v : Axis → Axis → L.Ref 4} (hJ : Conserved W H (draw S v))
    (hv : Motion i V) (hS : ∀ B : L.Ref d, Snip S v B D (3+i)) : ∃ Q : S.Field d →ₗ[ℂ] S.Field D, ∀ B, Represents (draw S v) B V (Q B) := by
  let J := draw S v
  have he (B : S.Field d) : ∃ u : S.Field D, Represents J B V u := by obtain ⟨b,rfl⟩ := S.onto d B; exact pick hs hd hJ b hv (hS b)
  choose q hq using he
  have ht (B : S.Field d) {n : ℕ} (x : Points (n+1)) (p : Fin n → S.Tag) χ (hx : x∈conf _) (hw : Window x χ) :
      frontRead p x D (q B) = shellMap hs.smooth J p _ hx hw (fun b => (hv.smooth b).continuous) B := (hq B n x p χ hx hw).symm
  refine ⟨{toFun:=q
           map_add':=fun p t => S.field_ext hs.laws.toSymmetric fun n s x hx => ?_
           map_smul':=fun c p => S.field_ext hs.laws.toSymmetric fun n s x hx => ?_},hq⟩
  · obtain ⟨χ,hχ⟩ := exists_window x hx
    simp_rw [← front_eval,map_add,ht _ x s χ hx hχ, map_add]
  obtain ⟨χ,hχ⟩ := exists_window x hx
  simp_rw [← front_eval,map_smul,ht _ x s χ hx hχ, map_smul]; rfl

abbrev turn (g : Ortho.Skew) : E4 → E4 := M4.move g.val

lemma constant_motion (b : E4) : Motion 0 (fun _ => b) := ⟨fun _ => contDiff_const,killing_const b,fun _ _ _ => (by simp)⟩
lemma turn_motion (g : Ortho.Skew) : Motion 1 (turn g) := by
  have he : turn g = orbital g 0 := by unfold orbital; simp only [sub_zero]
  exact ⟨he ▸ smooth_orbital g 0,he ▸ killing_orbital g 0,fun r _ z => by rw [pow_one]; exact map_smul (Matrix.toEuclideanLin g.val) r z⟩
lemma turn_add (g k : Ortho.Skew) (z : E4) : turn (g+k) z = turn g z + turn k z := by
  ext b; simp [turn,M4.at_coord,add_mul,Finset.sum_add_distrib]
lemma turn_smul (g : Ortho.Skew) (t : ℝ) (z : E4) : turn (t • g) z = t • turn g z := by
  ext b; simp [turn,M4.at_coord,mul_assoc,Finset.mul_sum]

lemma rotationMaps (hs : S.Hierarchy) (hd : W.Derivatives S) {v : Axis → Axis → L.Ref 4} (hJ : Conserved W H (draw S v))
    (hS : ∀ B : L.Ref d, Snip S v B d 4) : ∃ A : Ortho.Skew →ₗ[ℝ] (S.Field d →ₗ[ℂ] S.Field d), ∀ g B, Represents (draw S v) B (turn g) (A g B) := by
  choose Q hQ using fun g => linear hs hd hJ (turn_motion g) hS
  refine ⟨{toFun:=Q
           map_add':=fun p t => LinearMap.ext fun B => S.field_ext hs.laws.toSymmetric fun n s x hx => ?_
           map_smul':=fun c g => LinearMap.ext fun B => S.field_ext hs.laws.toSymmetric fun n s x hx => ?_},hQ⟩
  · obtain ⟨χ,hχ⟩ := exists_window x hx
    simp_rw [← front_eval,LinearMap.add_apply,map_add, ← show ∀ g, about _ χ _ _ s _=_ from fun g => hQ g B n x s χ hx hχ]
    let F g := term (draw S v) χ (fun y => turn g (y-x 0)) x s B
    have h (g : Ortho.Skew) a b : Integrable (F g a b) := term_integrable (draw S v) χ (fun y => turn g (y-x 0)) x s B hs.smooth hx hχ a b (((turn_motion g).smooth b).continuous.comp (continuous_id.sub continuous_const))
    have ht a b y : F (p+t) a b y = F p a b y + F t a b y := by simp [F,term, turn_add,mul_add,add_mul]
    change -(∑ a, ∑ b, ∫ y, F _ a b y)=-(∑ a, ∑ b, ∫ y, F _ a b y) + -(∑ a, ∑ b, ∫ y, F _ a b y)
    simp_rw [ht,integral_add (h p ..) (h t ..),Finset.sum_add_distrib]; abel
  obtain ⟨χ,hχ⟩ := exists_window x hx
  change _ = S.useAt S _ (Fin.cons ⟨d,c • Q g B⟩ s)
  rw [← front_eval,← front_eval, ← (hQ _ B _ _ s χ hx hχ), show frontRead s x d (c • Q g B) = c • frontRead s x d (Q g B) from ((frontRead s x d).restrictScalars ℝ).map_smul c _, ← (hQ _ B _ _ s χ hx hχ)]
  simp_rw [about,turn_smul,flux_scale]; rfl

theorem laws (hs : S.Hierarchy) (hd : W.Derivatives S) {v : Axis → Axis → L.Ref 4} (hJ : Conserved W H (draw S v))
    (he : ∀ d (B : L.Ref d), Snip S v B (d+1) 3 ∧ Snip S v B d 4) : ∃ p A, StressLaws S (draw S v) p A := by
  choose Q hQ using fun d (a : Axis) => linear hs hd hJ (constant_motion (basis a)) (fun B => (he d B).1)
  choose A hA using fun d => rotationMaps hs hd hJ (fun B => (he d B).2)
  refine ⟨Q,A,⟨fun {n x} hx q {_χ} w b d B => ?_,fun {n x} hx q {_χ} w g d B => ?_⟩⟩
  · exact (flux_translation ..).symm.trans ((hQ d b B n x q _ hx w).trans (front_eval ..))
  exact (hA d g B n x q _ hx w).trans (front_eval ..)
end YM.StressFlux.Annular
