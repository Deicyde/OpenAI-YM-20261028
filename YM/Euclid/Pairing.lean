import YM.Euclid.Words

/-!
# Pair test and its kernel reading

Use same index order in first test, permute back through `Symmetric`
at all distinct positions. (Permitting this only after smooth completion.)
-/
set_option autoImplicit false
noncomputable section
namespace YM.Table.Pairing
open Function Filter Set MeasureTheory Word WithLp
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius ComplexOrder

variable {G : Gauge} {L : Register G} {n m : ℕ} (a : Axis)

def ride (x : E4) := (Signed.reflect a).motion x
@[simp] lemma riding (x) : ride a (ride a x)=x := by ext i; by_cases h:i=a <;> simp [ride,h]

def earlier (x : Points (n+m)) := points fun i : Fin n => ride a (x (Fin.castAdd m i))
def after (x : Points (n+m)) := points fun i : Fin m => x (Fin.natAdd n i)

def glues : WithLp 2 (Points n × Points m) ≃ₗᵢ[ℝ] Points (n+m) where
  toFun p := points (Fin.append (fun i => ride a (p.fst i)) p.snd.ofLp)
  invFun p := toLp 2 (earlier a p,after p)
  left_inv p := by
    apply ofLp_injective 2; apply Prod.ext
    · apply PiLp.ext; intro i; simp [earlier]
    apply PiLp.ext; intro i; simp [after]
  right_inv p := by
    apply PiLp.ext; intro i; refine Fin.addCases ?_ ?_ i
    · intro i; simp [earlier]
    intro i; simp [after]
  map_add' p q := by
    apply PiLp.ext; intro i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [-Ortho.motion_at,ride]
  map_smul' p q := by
    apply PiLp.ext; intro i; refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp [-Ortho.motion_at,ride]
  norm_map' p := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)]
    rw [PiLp.norm_sq_eq_of_L2, WithLp.prod_norm_sq_eq_of_L2, PiLp.norm_sq_eq_of_L2 _ p.fst, PiLp.norm_sq_eq_of_L2 _ p.snd, Fin.sum_univ_add]
    simp [-Ortho.motion_at,ride]

def pairIso : Points (n+m) ≃L[ℝ] Points n × Points m :=
  ((glues a).symm).toContinuousLinearEquiv.trans (WithLp.prodContinuousLinearEquiv 2 ℝ (Points n) (Points m))

def closedUp (x : Points n) (y : Points m) := (pairIso a).symm (x,y)
@[simp] lemma enter (x : Points n) (y : Points m) (i) : closedUp a x y (Fin.castAdd m i) = ride a (x i) := by
  change points (Fin.append _ _) _ = _; simp
@[simp] lemma leave (x : Points n) (y : Points m) (i) : closedUp a x y (Fin.natAdd n i)= y i := by
  change points (Fin.append _ _) _ = _; simp
@[simp] lemma equals (x : Points (n+m)) : pairIso a x = (earlier (n := n) (m := m) a x,after (n := n) (m := m) x) := rfl

lemma volume_split : MeasurePreserving (pairIso a (n := n) (m := m)) :=
  (WithLp.volume_preserving_ofLp _ _).comp ((glues a).symm).measurePreserving

variable {a}

def tied (x : Fin n → L.Token) (y : Fin m → L.Token) (a : Axis) : Fin (n+m) → L.Token := Fin.append (L.reflectedToken a ∘ x) y

lemma flipped (w : Fin n → L.Token) (p : Fin m → L.Token) (x : Points n) (y : Points m) :
    (reflect (realize w x) a).reverse ++ realize p y = realize (tied w p a) (closedUp a x y) := by
  rw [reflectedPoint, List.map_reverse,List.reverse_reverse,realize,List.map_ofFn]
  unfold realize
  rw [← List.ofFn_fin_append]
  congr 1
  funext i; refine Fin.addCases ?_ ?_ i
  · intro i; simp [tied,ride]
  intro i; simp [tied]

def single (x : Points n) (a : Axis) := x ∈ conf n ∧ Points.allAbove a 0 x

lemma living (w : Fin n → L.Token) {x : Points n} (h : single x a) : Positive (realize w x) a := by
  refine ⟨(realized w _).2 h.1,?_⟩
  intro p hp
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hp
  rw [← hi]; exact h.2 i

lemma displacement (S : Table L) (H : S.Symmetric) (p : Fin n → L.Token) (q : Fin m → L.Token) {x y} (hp : single x a) (hq : single y a) :
    S.gram a (realize p x) (realize q y)=S.read (closedUp a x y) (tied p q a) := by
  rw [← readAt,← flipped]; symm
  apply S.order H (twoSides (living p hp) (living q hq))
  apply List.Perm.append_right _ (List.reverse_perm _).symm

lemma stays (Q : PastTest L a) {x} (hx : x∈ tsupport Q.f) : single x a :=
  ⟨Q.f.tsupport_subset hx,Q.past x hx⟩

lemma spans {x : Points n} {y : Points m} (hp : single x a) (hq : single y a) : closedUp a x y∈ conf _ := by
  -- direct coordinate proof
  intro i j he; revert he
  refine Fin.addCases ?_ ?_ i
  · intro i; refine Fin.addCases ?_ ?_ j
    · intro j h; rw [enter,enter] at h; rw [hp.1 ((Signed.reflect a).motion.injective h)]
    intro j h; rw [enter,leave] at h
    have ht := congr_arg (fun (x : E4) => x a) h
    simp [ride] at ht; have hh := hp.2 i; exact False.elim (by linarith [hq.2 j])
  intro i; refine Fin.addCases ?_ ?_ j
  · intro j h; rw [leave,enter] at h
    have ht := congr_arg (fun (x : E4) => x a) h
    simp [ride] at ht; have hh := hp.2 j; exact False.elim (by linarith [hq.2 i])
  intro j h; rw [leave,leave] at h; rw [hq.1 h]

/-- On actual tuples index order, conjugate test f; permute only once. -/
def samples (Q V : PastTest L a) (x : Points (Q.n+V.n)) :=
    star (Q.f (earlier a x)) * V.f (after x)

lemma forward (Q V : PastTest L a) : tsupport (samples Q V) ⊆
    pairIso a ⁻¹' (tsupport (Q.f) ×ˢ tsupport V.f) := by
  apply closure_minimal _ (((Q.f.hasCompactSupport.isClosed).prod V.f.hasCompactSupport.isClosed).preimage (pairIso a).continuous); intro x hx
  change star (Q.f (earlier a x)) * V.f (after x) ≠ 0 at hx
  exact ⟨subset_closure (fun w => hx (by rw [show Q.f (earlier a x)=0 from w]; simp)),subset_closure (right_ne_zero_of_mul hx)⟩

def withOther (Q V : PastTest L a) : Test (Q.n+V.n) :=
  ⟨samples Q V,(Complex.conjCLE.contDiff.comp (Q.f.contDiff.comp (contDiff_fst.comp (pairIso a).contDiff))).mul
    (V.f.contDiff.comp (contDiff_snd.comp (pairIso a).contDiff)),
    (((pairIso a).toHomeomorph.isCompact_preimage).2 (Q.f.hasCompactSupport.prod V.f.hasCompactSupport)).of_isClosed_subset (isClosed_tsupport _) (forward Q V),
    fun x hx => by
      have hh := forward Q V hx
      have he : x=closedUp a (earlier (n := Q.n) a x) (after (m := V.n) x) := ((pairIso a).symm_apply_apply x).symm
      exact he.symm ▸ spans (stays Q hh.1) (stays V hh.2) ⟩

lemma corresponding (S : Table L) (h : S.Symmetric) (Q V : PastTest L a) (x : Points Q.n) (y : Points V.n) :
    (withOther Q V) (closedUp a x y) * S.read (closedUp a x y) (tied Q.v V.v a) = S.smeared a Q V (x,y) := by
  have he : (withOther Q V) (closedUp a x y)=star (Q.f x)*V.f y := by
    change star (Q.f ((pairIso a) (closedUp a x y)).1) * V.f ((pairIso a) (closedUp a x y)).2=_
    unfold closedUp; rw [ContinuousLinearEquiv.apply_symm_apply]
  rw [he]; unfold smeared
  by_cases hv:x∈tsupport Q.f
  swap; rw [image_eq_zero_of_notMem_tsupport hv]; simp
  by_cases hx:y∈tsupport V.f
  swap; rw [image_eq_zero_of_notMem_tsupport hx]; simp
  rw [← displacement S h _ _ (stays Q hv) (stays V hx)]

lemma at_integral (S : Table L) (h : S.Symmetric) (_ : S.Smooth) (Q V : PastTest L a) :
    (withOther Q V).applyTo (fun x => S.read x (tied Q.v V.v a)) = ∫ x, S.smeared a Q V x := by
  rw [← MeasurePreserving.integral_comp (volume_split (n := Q.n) (m := V.n) a) (pairIso a).toHomeomorph.measurableEmbedding (S.smeared a Q V)]
  unfold Test.applyTo
  apply integral_congr_ae; filter_upwards with x
  have he := corresponding S h Q V ((pairIso a) x).1 ((pairIso a) x).2
  rwa [show closedUp a ((pairIso a) x).1 ((pairIso a) x).2=x from (pairIso a).symm_apply_apply _] at he

lemma pairedIntegrable (S : Table L) (h : S.Symmetric) (hs : S.Smooth) (Q V : PastTest L a) :
    Integrable (S.smeared a Q V) volume := by
  apply ((volume_split (n := Q.n) (m := V.n) a).integrable_comp_emb (pairIso a).toHomeomorph.measurableEmbedding).mp
  refine (Test.smearing (withOther Q V) (S.smooth_read hs (tied Q.v V.v a)).continuousOn).congr (Eventually.of_forall (fun x => ?_))
  have he := corresponding S h Q V ((pairIso a) x).1 ((pairIso a) x).2
  rwa [show closedUp a ((pairIso a) x).1 ((pairIso a) x).2=x from (pairIso a).symm_apply_apply _] at he
end YM.Table.Pairing
