import YM.Push.LOOP_COEFFICIENT.Block.Duplicate
import YM.Push.LOOP_COEFFICIENT.Block.Induce
import YM.Push.LOOP_COEFFICIENT.Block.Priced

/-!
# Shift-domain reparameterization helpers with dimension-free charge
-/
set_option autoImplicit false
noncomputable section
namespace YM.Push.Loops.Block
open Matrix Function Filter Set Lattice Laurent Bloch RG Precision Exterior Wilson Complex Portal Fine Paths
open scoped Topology ContDiff BigOperators Matrix.Norms.L2Operator
variable {a b c d : Type} [Fintype a] [Fintype b] [Fintype d] [DecidableEq a] [DecidableEq b] {L : Side} {X : Vertex d a b} {η e A B : ℝ}

def Grows (X : Vertex d a b) (η : ℝ) := StripLaw X (Tube η) (Tube η)
namespace Grows
omit [DecidableEq a] [Fintype d] in lemma of_lit (h : Lit X η) : Grows X η := StripLaw.of_lit h (Subset.refl _) (Subset.refl _)
omit [DecidableEq a] [Fintype d] in
lemma mono (h : Grows X η) (he : e≤η) : Grows X e :=
    let he := tube_mono he
    ⟨fun _ hq => h.base _ (he hq),fun _ _ _ hq hp => h.one _ _ _ ⟨he hq.1,he hq.2⟩ (he hp),fun _ _ _ _ _ hq hp hs => h.two _ _ _ _ _ ⟨he hq.1,he hq.2.1,he hq.2.2.1,he hq.2.2.2⟩ (he hp) (he hs)⟩
omit [DecidableEq a] [Fintype d] in lemma const (M : Matrix a b ℂ) : Grows (Vertex.const (d:=d) fun _ => M) η := StripLaw.const fun _ _ => ⟨contDiffAt_const,by intros; rfl⟩
omit [Fintype d] in lemma id : Grows (Vertex.id (d:=d) (a:=a)) η := Grows.const _
private lemma recv (p q : Momentum) (x y : Cover) : p+reciprocal x+(q+reciprocal y)=p+q+reciprocal (x+y) := by rw [reciprocal_add]; abel
private lemma recv' (p : Momentum) (x : Cover) : -(p+reciprocal x)=-p+reciprocal (-x) := by rw [reciprocal_neg]; abel
omit [Fintype d] in lemma transpose (h : Grows X η) : Grows X.transpose η := by
  constructor
  · intro q hq; refine ⟨analyticTranspose (h.zeroD (q:=(-·)) (by fun_prop) (tube_neg hq)),fun x => congr_arg Matrix.transpose ?_⟩; rw [recv',(h.base _ (tube_neg hq)).2]
  · intro q p v hq hp; refine ⟨analyticTranspose (h.oneD (q:=fun x => -(x.1+x.2)) (p:=Prod.snd) (by fun_prop) contDiffAt_snd (neg_active₁ hq) hp v), fun x y => congr_arg Matrix.transpose ?_⟩; rw [recv,recv',(h.one _ _ _ (neg_active₁ hq) hp).2]
  intro q p s v w hq hp hs; refine ⟨analyticTranspose (h.twoD (q:=fun x : Momentum × Momentum × Momentum => -(x.1+x.2.1+x.2.2)) (p:=fun x => x.2.1) (s:=fun x => x.2.2) (x:=(q,p,s)) (by fun_prop) (by fun_prop) (by fun_prop) (neg_active₂ hq) hp hs v w), fun x y z => congr_arg Matrix.transpose ?_⟩; rw [recv,recv,recv',(h.two _ _ _ _ _ (neg_active₂ hq) hp hs).2]
lemma duplicate {G : Gauge} {X : Vertex (Axes G) (ScalarBlock G L) (ScalarBlock G L)} (h : Grows X η) : Grows (Block.duplicate X) η := by
  let A := (install G L).toContinuousLinearMap
  exact ⟨fun _ hq => ⟨A.contDiff.contDiffAt.comp _ (h.base _ hq).1,fun _ => congr_arg (install G L) ((h.base _ hq).2 _)⟩,
    fun q p v hq hp => ⟨A.contDiff.contDiffAt.comp (f:=fun z : Momentum × Momentum => X.one z.1 z.2 v) (q,p) (h.one q p v hq hp).1, fun _ _ => congr_arg (install G L) ((h.one _ _ _ hq hp).2 ..)⟩,
    fun q p s v w hq hp hs => ⟨A.contDiff.contDiffAt.comp (f:=fun z : Momentum × Momentum × Momentum => X.two z.1 z.2.1 z.2.2 v w) (q,p,s) (h.two q p s v w hq hp hs).1, fun _ _ _ => congr_arg (install G L) ((h.two _ _ _ _ _ hq hp hs).2 ..)⟩⟩
end Grows




omit [Fintype d] [DecidableEq a] in
lemma rep_opposite {U : Vertex d a b} (he : Lit U (η/L.val)) {q : Momentum} (hq : q∈Tube η) (l : Site L) : U.base (-aliasAt q l) = U.base (aliasAt (-q) (-l)) := by obtain ⟨x,hx⟩ := alias_opposite l q; rw [hx,(he.base _ (tube_neg (alias_tube l hq))).2]

variable {J E F H : Type} [Fintype J] [Fintype E] [Fintype F] [Fintype H] [DecidableEq J] [DecidableEq E] [DecidableEq F] [DecidableEq H] [Fintype c] [DecidableEq c] [DecidableEq d]
  {s f : Side} {g : Ratio s f} {K : Grid s J c} {T : Grid f H d} {M : Grid f E a} {N : Grid f F b}
open scoped Matrix.Norms.Frobenius in
omit [DecidableEq E] [DecidableEq F] in
lemma induce_models {Z : (H → ℝ) → Matrix E F ℝ} {P : Matrix H J ℝ} {Y : Loops.Profiles g.count d c} (h : Models T M N Z X) (hP : Projects g T K (cmat P) Y) : Models K (M.trans (splitCo g a)) (N.trans (splitCo g b)) (fun z => Z (P *ᵥ z)) (induce X Y) := by
  let W := P.mulVecLin.toContinuousLinearMap; have he : ContDiffAt ℝ ω Z (W 0) := by rw [W.map_zero]; exact h.smooth
  exact ⟨he.comp 0 W.contDiff.contDiffAt,by rw [actualMatrix_pre h.smooth]; exact induce_synced h.sync hP⟩
end YM.Push.Loops.Block
