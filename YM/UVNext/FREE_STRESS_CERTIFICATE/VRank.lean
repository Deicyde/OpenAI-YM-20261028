import YM.UVNext.FREE_STRESS_CERTIFICATE.VSpan

/-! Actual Bianchi/Maxwell collapse through five on the quotient. -/
set_option autoImplicit false
noncomputable section
namespace YM.UVNext.FreeStress
open Maxwell Labels Tensor Analysis Climb Table Work.A01 Next.UVStress Function Set Submodule
variable {G : Gauge} (F : Frames G) (H : (freeTable F).RealSpin) {d : ℕ} (hG : G.Simple)

lemma disappears (P : Label G d) (h : ∀ X : Maxwell.TaylorTower G, Labels.read (fun i => gaugeJet (X i)) P.val = 0) :
    embed F d P=0 := by
  have hP : observable G d P=0 := Maxwell.ideal_meaning.mpr h
  apply (freeTable F).faithfully; rw [map_zero]; funext x
  change (freeTable F).read x.point (Fin.cons (token F d P) x.letter) = 0
  rw [first_label,hP]; exact (moment_at_zero ..)
where
  moment_at_zero (n : ℕ) (x : Points (n+1)) (f : Fin n → WickPol G) : Wick.moment G x (Fin.cons 0 f) = 0 :=
    (Wick.moment G x).map_coord_zero 0 (Fin.cons_zero ..)

private lemma oneJet (f : Tensor.T E4 G.Color 1) (i : Axis) (x) :
    Maxwell.grad i (Tensor.diagonal f) x = f (fun _ => YM.basis i) := by
  have he : Tensor.Sym f := fun v p => congr_arg f (funext fun j => congr_arg v (Subsingleton.elim (p j) j))
  change fderiv ℝ (Tensor.diagonal f) x _ = _
  rw [Tensor.differential_diagonal (j:=0) f he x]
  simp only [Nat.zero_add, one_smul, ContinuousMultilinearMap.curryLeft_apply]
  exact congr_arg f (funext fun j => by rw [@Subsingleton.elim (Fin 1) _ j 0]; rfl)

def coarse (X : Maxwell.TaylorTower G) (a b : Axis) : G.Color := ((X 0).val a b) (fun _ => 0)
def wave (X : Maxwell.TaylorTower G) (a b c : Axis) : G.Color := ((X 1).val a b) (fun _ => YM.basis c)

lemma cycle_wave (X : Maxwell.TaylorTower G) (a b c : Axis) : wave X b c a + wave X c a b + wave X a b c = 0 := by
  have h := (show Maxwell.ClosedJet (X 1).val from (X 1).property.1).closed a b c 0
  simpa only [oneJet,wave] using h
lemma silence (X : Maxwell.TaylorTower G) (a : Axis) : ∑ b : Axis, wave X b a b = 0 := by
  have h := (X 1).property.2 a 0
  simpa only [oneJet,wave] using h

lemma air_eval (X : Maxwell.TaylorTower G) (a b c e i : Axis) :
    Labels.read (fun k => gaugeJet (X k)) (fq G 5 le_rfl a b c e i).val = (inner ℝ (coarse X a b) (wave X c e i):ℂ) := by
  unfold fq bond
  rw [eval_tape]
  simp only [component, LinearMap.coe_mk, AddHom.coe_mk, match_leg]
  unfold coarse wave
  rw [show YM.basis ∘ (Fin.elim0 : Fin 0 → Axis) = fun _ => (0:E4) from Subsingleton.elim ..]
  rfl

lemma clears (a b c : Axis) : ∑ i, first F a b i c i = 0 := by
  unfold first
  simp_rw [← map_sum]
  apply disappears; intro X
  simp only [AddSubmonoidClass.coe_finsetSum,map_sum,air_eval]
  rw [← Complex.ofReal_sum]
  have h := congr_arg (innerₛₗ ℝ (coarse X a b)) (silence X c)
  rw [map_sum,map_zero] at h
  rw [show (∑ i : Axis, inner ℝ (coarse X a b) (wave X i c i))=0 from h]; simp

lemma spins (a b i j k : Axis) : first F a b j k i + first F a b k i j + first F a b i j k = 0 := by
  unfold first; simp_rw [← map_add]
  apply disappears; intro X
  simp only [Submodule.coe_add,map_add,air_eval,← Complex.ofReal_add]
  have h := congr_arg (innerₛₗ ℝ (coarse X a b)) (cycle_wave X i j k)
  simp only [map_add,map_zero] at h
  -- mixed RHS want cast add
  have hw : inner ℝ (coarse X a b) (wave X j k i) + inner ℝ (coarse X a b) (wave X k i j) + inner ℝ (coarse X a b) (wave X i j k)=0 := h
  rw [hw]; simp

-- equations on the orbit classes; explicit axis arithmetic then simplify by
-- antisymmetry. 
lemma arms_eq : nose F + arms F = 0 := by
  unfold nose arms; rw [single_eval,pair_eval]
  have h (b : Axis) := clears F 0 b b
  simp_rw [Fin.sum_univ_succ] at h
  have h1 := h 1; have h2 := h 2; have h3 := h 3
  -- normal reduction of succ representation
  norm_num [Fin.isValue, Fin.reduceFinMk] at h1 h2 h3
  simp only [show (2 : Fin 3).succ=(3:Fin 4) from rfl, first_zeroR,add_zero] at h1 h2 h3
  linear_combination (norm:=abel) h1 + h2 + h3

lemma chirp (i j : Axis) : first F j i 0 i j + first F i j 0 j i = first F i j i j 0 := by
  have h := spins F i j j 0 i -- 0 i j + i j 0 + j 0 i
  rw [right_first F i j 0 j i] at h
  rw [left_first F i j]
  linear_combination (norm:=abel) -h

lemma twice_hands : hands F + hands F = chin F := by
  have h (i j : Axis) := chirp F i j
  unfold hands chin; rw [pair_eval,pair_eval]
  linear_combination (norm:=abel) h 2 1 + h 1 2 + h 1 3 + h 3 1 + h 3 2 + h 2 3

include hG in
theorem two_v (v : Vectors H) : v.val 0 ∈ span ℝ {nose F,hands F} := by
  apply (show span ℝ {nose F,chin F,arms F,hands F} ≤ span ℝ {nose F,hands F} from span_le.mpr ?_) (real_v F H hG v)
  intro y hy
  have h1 : nose F ∈ span ℝ {nose F,hands F} := subset_span (by simp)
  have h2 : hands F ∈ span ℝ {nose F,hands F} := subset_span (by simp)
  simp only [mem_insert_iff,mem_singleton_iff] at hy; rcases hy with rfl|rfl|rfl|rfl
  · exact h1
  · rw [← twice_hands]; exact Submodule.add_mem _ h2 h2
  · rw [eq_neg_of_add_eq_zero_right (arms_eq F)]; exact Submodule.neg_mem _ h1
  exact h2

include hG in
/-- Finite upper bound; rank lower and exactness by separated curl derivatives. -/
theorem capped_v : Module.finrank ℝ (Vectors H) ≤ 2 := by
  let f : (Vectors H) →ₗ[ℝ] FiveFields F := (LinearMap.proj (0:Axis)).comp (Vectors H).subtype
  let g := f.codRestrict (span ℝ {nose F,hands F}) (fun v => two_v F H hG v)
  have he : Injective g := by
    intro v w hh
    have h : v.val 0 = w.val 0 := congr_arg Subtype.val hh
    apply Subtype.ext; funext a
    have ht := congr_arg (ride F H 5 (Equiv.swap 0 a)) h; simpa only [perm_v,Equiv.swap_apply_left] using ht
  refine (LinearMap.finrank_le_finrank_of_injective he).trans ?_
  classical
  have hi := finrank_span_finset_le_card (R:=ℝ) ({nose F, hands F} : Finset (FiveFields F))
  simp only [Finset.coe_insert,Finset.coe_singleton] at hi
  exact hi.trans ((Finset.card_insert_le ..).trans_eq (by simp))

end YM.UVNext.FreeStress
