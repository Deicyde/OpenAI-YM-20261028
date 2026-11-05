import YM.Next.UV_STRESS.Rates

/-!
# Exact common filtration adjustment (before implementing derivative labels)

Use H-real splitting. The coordinates at weight d+1 need *not* agree
with those at d. Put the weak panel on the complement only, using the joint
bounds (below) with all of the actual weights.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Filter Function Set Analysis Extraction Table Ward Climb
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {L : Register G} {T : Table L} {C : Family G} {S : Table C.book} {F : Order}
variable {W : DiffPlan S} {V : DiffPlan (Bel C.book)}

section Split
-- equivariant retraction
variable {P : DiffPlan T} {H : T.Hierarchy} {d e : ℕ} (u : d ≤ e)

private def averaged (H : T.RealSpin) (f : T.Field e →ₗ[ℂ] T.Field d) (i : Signed) : T.Field e →ₗ[ℂ] T.Field d :=
    (T.mirror H d i⁻¹).comp (f.comp (T.mirror H e i))

private def dualConjugate (H : T.RealSpin) (f : T.Field e →ₗ[ℂ] T.Field d) : T.Field e →ₗ[ℂ] T.Field d :=
    (T.conj H d).comp (f.comp (T.conj H e))

lemma signed_section (h : P.Inclusions T) (hc : P.Orientation H.spin) :
    ∃ R : T.Field e→ₗ[ℂ] T.Field d, (∀ x, R (P.rise u x)=x) ∧
      (∀ x, R (T.conj H.spin e x)=T.conj H.spin d (R x)) ∧
      (∀ i x, R (T.mirror H.spin e i x)=T.mirror H.spin d i (R x)) := by
  obtain ⟨g,hg⟩ := (P.rise u).exists_leftInverse_of_injective
    (LinearMap.ker_eq_bot.mpr (P.inject H.laws.toSymmetric h u))
  have he x : g (P.rise u x)=x := LinearMap.congr_fun hg x
  let f := ((2:ℂ)⁻¹) • (g + dualConjugate H.spin g)
  have hf x : f (P.rise u x)=x := by
    change ((2:ℂ)⁻¹ • (g + dualConjugate H.spin g)) _ = _
    simp_rw [LinearMap.smul_apply, LinearMap.add_apply, he]
    change ((2:ℂ)⁻¹) • (x + T.conj H.spin _ (g (T.conj H.spin _ (P.rise u x))))=_
    rw [hc.realInc, he, T.reflect_star]
    have ht : x+x=(2:ℂ) • x := by rw [show (2:ℂ)=1+1 by norm_num, add_smul,one_smul]
    rw [ht, smul_smul, inv_mul_cancel₀ (by norm_num), one_smul]
  have ha x : f (T.conj H.spin e x)=T.conj H.spin d (f x) := by
    change ((2:ℂ)⁻¹ • (g (T.conj H.spin e x) + T.conj H.spin d (g (T.conj H.spin e (T.conj H.spin e x)))))= T.conj H.spin d ((2:ℂ)⁻¹ • (g x + T.conj H.spin d (g (T.conj H.spin e x))))
    simp only [T.reflect_star,map_smulₛₗ,map_add]; congr 1
    · rw [map_inv₀, show (2:ℂ)=1+1 by norm_num,map_add,map_one]
    abel
  let p : ℂ := Fintype.card Signed
  have hp : p ≠ 0 := Nat.cast_ne_zero.mpr (pos_iff_ne_zero.mp
    (show 0 < Fintype.card Signed from Fintype.card_pos))
  let r := averaged H.spin f
  let R := p⁻¹ • ∑ i : Signed,r i
  have hh x : R x=p⁻¹ • ∑ i : Signed, r i x := by simp [R]
  have hs i x : r i (P.rise u x)=x := by
    change T.mirror H.spin d i⁻¹ (f (T.mirror H.spin e i (P.rise u x)))=_
    rw [hc.mirrorInc,hf,← T.mirror_mul,inv_mul_cancel,T.mirror_one]
  have hr i x : r i (T.conj H.spin e x)=T.conj H.spin d (r i x) := by
    change T.mirror H.spin d i⁻¹ (f (T.mirror H.spin e i (T.conj H.spin e x)))=
      T.conj H.spin d (T.mirror H.spin d i⁻¹ (f (T.mirror H.spin e i x)))
    rw [← T.mirror_star,ha,T.mirror_star]
  refine ⟨R,fun x => ?_,fun x => ?_,fun i x => ?_⟩
  · rw [hh]; simp_rw [hs,Finset.sum_const,Finset.card_univ]
    rw [show Fintype.card Signed • x=p • x from (Nat.cast_smul_eq_nsmul ℂ _ _).symm,
      smul_smul, inv_mul_cancel₀ hp, one_smul]
  · rw [hh,hh,map_smulₛₗ,map_sum]; simp_rw [hr]; simp [p]
  have hx (k : Signed) : r k (T.mirror H.spin _ i x)=T.mirror H.spin _ i (r (k*i) x) := by
    change T.mirror H.spin d k⁻¹ (f (T.mirror H.spin e k (T.mirror H.spin e i x)))=
      T.mirror H.spin d i (T.mirror H.spin d (k*i)⁻¹ (f (T.mirror H.spin e (k*i) x)))
    rw [← T.mirror_mul,← T.mirror_mul,mul_inv_rev,← mul_assoc,mul_inv_cancel,one_mul]
  rw [hh,hh,map_smul,map_sum]; simp_rw [hx]; refine congr_arg (p⁻¹ • ·) (?_ : (∑ k : Signed, T.mirror H.spin d i (r (k*i) x)) = ∑ k : Signed,T.mirror H.spin d i (r k x))
  exact Equiv.sum_comp (Equiv.mulRight i) (fun k => T.mirror H.spin d i (r k x))
end Split

abbrev Drop (T : Table L) := ∀ d : ℕ,T.Field (d+1) →ₗ[ℂ] T.Field d
abbrev adjStep (P : DiffPlan T) (d : ℕ) := P.rise (Nat.le_succ d)

def corrected (W : DiffPlan S) (V : DiffPlan (Bel C.book)) (R : Drop (Bel C.book)) (U : Panel S) : Panel S
  | 0 => U 0
  | d+1 =>
    (adjStep W d).comp ((corrected W V R U d).comp (R d)) + (U (d+1)).comp (LinearMap.id - (adjStep V d).comp (R d))

lemma correction (W : DiffPlan S) (V : DiffPlan (Bel C.book)) (R : Drop (Bel C.book)) (U : Panel S) (d x) :
    corrected W V R U (d+1) x = adjStep W d (corrected W V R U d (R d x)) + U (d+1) (x-adjStep V d (R d x)) := by
  rw [corrected]; rfl

lemma solid {H : S.Hierarchy} {a : (Bel C.book).Hierarchy} (U : ℕ → Panel S)
    (hW : W.Orientation H.spin) (hV : V.Orientation a.spin) (R : Drop (Bel C.book))
    (hR : ∀ d x, R d ((Bel C.book).conj a.spin (d+1) x)=(Bel C.book).conj a.spin d (R d x))
    (hM : ∀ d i x, R d ((Bel C.book).mirror a.spin (d+1) i x)=(Bel C.book).mirror a.spin d i (R d x))
    (hu : ∀ d, ∀ᶠ k in atTop,StraightAt H.spin a.spin (U k) d) :
    ∀ d, ∀ᶠ k in atTop, StraightAt H.spin a.spin (corrected W V R (U k)) d := by
  intro d; induction d with
  | zero =>
    filter_upwards [hu 0] with k hk
    constructor
    · intro v; simp only [corrected]; exact hk.bars _
    intro v x; simp only [corrected]; exact hk.reflects ..
  | succ d ih =>
    filter_upwards [hu (d+1),ih] with k hk hp
    constructor
    · intro x
      rw [correction,correction,hR,hp.bars]
      unfold adjStep; rw [← hV.realInc,← map_sub,hk.bars,map_add,hW.realInc]
    intro i x
    rw [correction,correction,hM,hp.reflects]
    unfold adjStep; rw [← hV.mirrorInc,← map_sub,hk.reflects,map_add,hW.mirrorInc]

lemma balanced (H : S.Hierarchy) (a : (Bel C.book).Hierarchy) (U : Panel S)
    (hW : W.Inclusions S) (hV : V.Inclusions (Bel C.book)) (R : Drop (Bel C.book))
    (hR : ∀ d x, R d (adjStep V d x)=x) :
    ∀ (d e : ℕ) (w : d≤e) x, corrected W V R U e (V.rise w x) = W.rise w (corrected W V R U d x) := by
  intro d e w x; induction e,w using Nat.le_induction with
  | base => rw [V.arrival a.laws.toSymmetric hV, W.arrival H.laws.toSymmetric hW]
  | succ e he ih =>
    rw [show V.rise _ x = adjStep V e (V.rise he x) from (V.transit a.laws.toSymmetric hV he (Nat.le_succ e) _).symm]
    rw [correction,hR,sub_self,map_zero,add_zero,ih]
    exact W.transit H.laws.toSymmetric hW he (Nat.le_succ e) _

-- Transfer of the estimate through correction, including mixed tables of
-- different filtration grades (no limit of transition matrices needed).
variable {n : ℕ} {U : ℕ → Panel S}

private def hybr (X : Zoom) (U J : ℕ → Panel S) (I : Finset (Fin n)) (v : Fin n → (Bel C.book).Tag) (k : ℕ) (x : Points n) :=
    disc (fun i => panels (if i∈I then J k else U k) (v i)) (X.r k • x) - disc v x

private lemma smooth_hybr (X : Zoom) (U J : ℕ → Panel S) (I : Finset (Fin n)) (v : Fin n → (Bel C.book).Tag) (k : ℕ)
    (hs : S.Smooth) (ht : (Bel C.book).Smooth) : ContDiffOn ℝ ∞ (hybr X U J I v k) (conf n) :=
  (smoothZoom hs _ (X.positive k)).sub (smoothDisc ht _)

-- extend to one additional updated tag
private lemma changes (H : S.Hierarchy) (a : (Bel C.book).Hierarchy) (hW : W.Inclusions S) (hV : V.Inclusions (Bel C.book))
    (X : Zoom) (R : Drop (Bel C.book)) (U : ℕ→ Panel S)
    (I : Finset (Fin n)) (i : Fin n) (ht : i∉I) :
    let J k := corrected W V R (U k)
    (∀ v, Fades (hybr X U J I v)) →
    ∀ d x (v : Fin n→(Bel C.book).Tag), Fades (hybr X U J (insert i I) (update v i ⟨d,x⟩)) := by
  intro J he d; induction d with
  | zero =>
    intro x v
    let t := update v i (⟨0,x⟩ : (Bel C.book).Tag)
    refine (he t).congr (fun k => smooth_hybr X U J _ _ _ H.smooth a.smooth) (Eventually.of_forall (fun k y hy => ?_))
    unfold hybr
    apply congr_arg (·- disc t y)
    apply congr_arg (disc · (X.r k • y)); funext j
    by_cases h : j=i
    · subst j; unfold t; simp only [update_self,Finset.mem_insert_self, ↓reduceIte,ht]
      simp only [J,panels,corrected]
    dsimp only [t]; simp only [Finset.mem_insert,h,false_or]
  | succ d IH =>
    intro x v
    let w := update v i (⟨d+1,x⟩ : (Bel C.book).Tag)
    let p := R d x
    let q := x-adjStep V d p
    let g := update v i (⟨d,p⟩ : (Bel C.book).Tag)
    let P := update v i (⟨d+1,q⟩ : (Bel C.book).Tag)
    let L := insert i I
    have ha := IH p v
    have hb := he P
    refine (ha.plus hb).congr (fun k => smooth_hybr X U J _ _ _ H.smooth a.smooth) (Eventually.of_forall (fun k y hy => ?_))
    let z := X.r k • y
    let f (I : Finset (Fin n)) (v : Fin n → (Bel C.book).Tag) (i : Fin n) := panels (if i∈I then J k else U k) (v i)
    have hp (m x) : f L (update v i (⟨m,x⟩:(Bel C.book).Tag)) = update (f I v) i ⟨m,J k m x⟩ := by
      funext j
      by_cases h : j=i
      · subst j; simp only [f,L,Finset.mem_insert_self, update_self,↓reduceIte]; rfl
      simp [h, f,L]
    have hF : f I P=update (f I v) i ⟨d+1,U k (d+1) q⟩ := by
      funext j; by_cases h : j=i
      · subst j; simp only [f,P,update_self,ht, ↓reduceIte]; rfl
      simp [h,P,f]
    have hg : disc w y = disc g y + disc P y := by
      have hg : disc g y = here v y i (d+1) (adjStep V d p) := by
        rw [takes]; exact (V.inclusion_slot hV a.laws.toSymmetric (Nat.le_succ d) hy i v p).symm
      unfold w; rw [← takes, hg]; unfold P; rw [← takes,← map_add]
      exact congr_arg _ (by unfold q; abel)
    have hD : disc (f L w) z=disc (f L g) z + disc (f I P) z := by
      unfold w g; rw [hp,hp,hF]
      unfold J
      rw [correction]
      rw [← takes, map_add, takes]
      congr 1
      · exact W.inclusion_slot hW H.laws.toSymmetric (Nat.le_succ d) ((enlarged (X.positive k) y).1 hy) ..
      exact takes ..
    change (disc (f L g) z - disc g y) + (disc (f I P) z - disc P y) = disc (f L w) z-disc w y
    rw [hg,hD]; ring

lemma adjusts (H : S.Hierarchy) (a : (Bel C.book).Hierarchy) (hW : W.Inclusions S) (hV : V.Inclusions (Bel C.book))
    (X : Zoom) (R : Drop (Bel C.book)) (ht : Approaches X U) :
    Approaches X (fun k => corrected W V R (U k)) := by
  let J k := corrected W V R (U k)
  constructor; intro n v
  have hh (I : Finset (Fin n)) (v : Fin n → (Bel C.book).Tag) : Fades (hybr X U J I v) := by
    induction I using Finset.induction_on generalizing v with
    | empty =>
      convert ht.values n v using 1
      unfold hybr; simp; rfl
    | @insert i s h ih =>
      have hu := changes H a hW hV X R U s i h ih (v i).1 (v i).2 v
      rw [show update v i (⟨(v i).1,(v i).2⟩:(Bel C.book).Tag) = v from update_eq_self ..] at hu
      exact hu
  convert hh Finset.univ v using 1
  unfold hybr; simp; rfl
end YM.Next.UVStress
