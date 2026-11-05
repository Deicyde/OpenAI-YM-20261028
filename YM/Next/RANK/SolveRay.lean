import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import YM.Next.RANK.Along
import YM.Next.RANK.Peano

/-!
# Polynomial calibration budget along a test

Before suppressing nonlinear transport, Taylor ray and the solver are linked.
Uniformity in H.radius keeps the gate to be only post-L once, not once per
particle/path. Lean real-vector estimate even with complex data. Assumes FULL
poly reads, not some different prelimit regulator. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Spindle
open Lattice RG Wilson Asymptotics Filter Set Function MvPolynomial Normal Rise Common
open scoped Classical Matrix.Norms.Frobenius Topology ContDiff BigOperators

variable {A B : Type}

def walked (U : A → ℝ → ℂ) (P : poly A) (r : ℝ) := MvPolynomial.aeval (fun i=> U i r) P

lemma walks (U : A→ℝ→ℂ) (n : ℕ) (H : ∀ i, ContDiffAt ℝ n (U i) 0) (P : poly A) : ContDiffAt ℝ n (walked U P) 0 := by
  induction P using MvPolynomial.induction_on with
  | C a => unfold walked; simp only [MvPolynomial.aeval_C]; exact contDiffAt_const
  | add p q hp hq =>
    rw [show walked U (p+q)=walked U p+ walked U q from funext fun r=>map_add _ p q]; exact hp.add hq
  | mul_X p i hp =>
    unfold walked; simp only [map_mul, MvPolynomial.aeval_X]; exact hp.mul (H i)

lemma register_link (U : A→ℝ→ℂ) (d i : ℕ) (h : ∀ i,ContDiffAt ℝ d (U i) 0) (hx : i ≤ d) :
    ∃ E : poly A →ₗ[ℂ] ℂ, ∀ p:poly A, E p = iteratedDeriv i (walked U p) 0 := by
  refine ⟨{ toFun p := iteratedDeriv i (walked U p) 0
            map_add' := ?_
            map_smul' := ?_ }, fun _=>rfl⟩
  · intro p q
    rw [show walked U (p+q)=walked U p+ walked U q from funext fun r => _root_.map_add _ p q]
    exact iteratedDeriv_add ((walks _ _ h _).of_le (by exact_mod_cast hx)) ((walks _ _ h _).of_le (by exact_mod_cast hx))
  intro a p
  rw [show walked U (a • p)= a • walked U p from funext fun r => map_smul _ a p, iteratedDeriv_const_smul ((walks _ _ h _).of_le (by exact_mod_cast hx))]; rfl

abbrev smooth (d : ℕ) (f : ℝ→ℂ) (b : ℝ) := ContDiffAt ℝ d f 0 ∧ ∀ i,i ≤ d→ slopeCap i f 0≤ b
private lemma pollen (d : ℕ) : ∃ C : ℝ, 1 ≤ C ∧ ∀ f g A B, 0≤A→0≤B→ smooth d f A→ smooth d g B → smooth d (f*g) (C*A*B) := by
  let C (j : ℕ):= ∑ i∈Finset.range (j+1), (j.choose i:ℝ)
  let M:= 1+∑ i∈Finset.range (d+1), C i
  have h i : 0 ≤ C i := by unfold C; positivity
  have he := (show 0≤∑ i∈Finset.range (d+1), C i from Finset.sum_nonneg fun i _ => h i)
  refine ⟨M,le_add_of_nonneg_right he,fun f g A B ha hb ⟨hp,hA⟩ ⟨hg,hB⟩ => ⟨hp.mul hg,fun i hi=>?_⟩⟩
  have hl := Finset.single_le_sum (fun i _ => h i) (Finset.mem_range.mpr (Nat.lt_succ_of_le hi))
  apply (times_slope i (hp.of_le (by exact_mod_cast hi)) (hg.of_le (by exact_mod_cast hi))).trans
  calc
    _ ≤ ∑ j∈ Finset.range (i+1), (i.choose j:ℝ)*A*B := by
      apply Finset.sum_le_sum; intro j hj
      exact mul_le_mul (mul_le_mul_of_nonneg_left (hA j ((Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hi))
        (by positivity)) (hB _ (by omega)) (slope_pos ..) (by positivity)
    _ = C i * A * B := by unfold C; simp only [Finset.sum_mul]
    _ ≤ M * A * B := by
      apply mul_le_mul_of_nonneg_right _ hb
      apply mul_le_mul_of_nonneg_right _ ha
      unfold M; linarith only [hl]

private lemma collars (d : ℕ) (x y : ℝ→ℂ) (a b : ℝ) (hx : smooth d x a) (hy : smooth d y b) : smooth d (x+y) (a+b) := by
  refine ⟨hx.1.add hy.1,fun i hi=>?_⟩
  rw [slopeCap,iteratedFDeriv_add_apply (hx.1.of_le (by exact_mod_cast hi)) (hy.1.of_le (by exact_mod_cast hi))]
  apply (norm_add_le ..).trans (add_le_add (hx.2 i hi) (hy.2 i hi))

section
variable (U V : A → ℝ → ℂ) (j : ℕ) (c t : ℝ) (hc : 1 ≤ c) (ht : 0 ≤ t)

structure OrderedAt : Prop where
  east i : smooth j (U i) c
  west i : smooth j (V i) c
  bar i : smooth j (U i-V i) (c*t)

private lemma plants (j n : ℕ) : ∃ C : ℝ, 1≤C ∧ ∀ (A B : Type) (U V : A → ℝ → ℂ),∀ c t,1 ≤ c → 0 ≤ t → OrderedAt U V j c t →
    ∀ (p : Finset B) (x : B→A), p.card ≤ n → smooth j (walked U (glyphs x p)) (C*c^n) ∧ smooth j (walked V (glyphs x p)) (C*c^n) ∧
      smooth j (walked U (glyphs x p)-walked V (glyphs x p)) (C*c^n*t) := by
  have hconst (k : ℕ) (c : ℂ) : slopeCap k (fun (_ : ℝ) => c) 0 ≤ ‖c‖ := by by_cases hk:k=0; · subst k; rw [slope0]
                                                                            unfold slopeCap; rw [iteratedFDeriv_const_of_ne hk]; exact (show ‖(0:(ℝ [×k]→L[ℝ] ℂ))‖ ≤ ‖c‖ by simp)
  have hz (c : ℂ) (n : ℕ) (a : ℝ) (hc : ‖c‖ ≤ a) : smooth n (fun _=> c) a := ⟨contDiffAt_const,fun i _=> (hconst i c).trans hc⟩
  have hZ (A B : Type) (U : A → ℝ→ℂ) (g : B→A) : walked U (glyphs g ∅)=fun _=>1 := by funext i; simp only [walked,glyphs,Finset.prod_empty,map_one]
  induction n with
  | zero =>
    refine ⟨1,le_rfl,fun A B U V c t hc ht h p s hp=>?_⟩
    rw [Finset.card_eq_zero.mp (Nat.eq_zero_of_le_zero hp),hZ A B,hZ A B,sub_self]; exact ⟨hz 1 _ _ (by simp),hz 1 _ _ (by simp),hz 0 _ _ (by simp [ht])⟩
  | succ n H =>
    obtain ⟨C,hc,Hc⟩ := H
    obtain ⟨J,hJ,H⟩:=pollen j
    let T:= 2*J*C
    have he : J*C≥1 := one_le_mul_of_one_le_of_one_le hJ hc
    have hh : 1≤T := by dsimp only [T]; linarith only [he]
    refine ⟨T,hh,fun A B U V v t hv ht h p f hp => ?_⟩
    obtain hp|⟨i,hi⟩ := p.eq_empty_or_nonempty
    · subst p; rw [hZ A B,hZ A B,sub_self]; have hb : 1 ≤ T*v^(n+1) := one_le_mul_of_one_le_of_one_le hh (one_le_pow₀ hv)
      have hz' := (show ‖(1:ℂ)‖ ≤ _ from norm_one.trans_le hb)
      exact ⟨hz _ _ _ hz', hz _ _ _ hz', hz 0 _ _ (by simp only [norm_zero]; exact mul_nonneg (zero_le_one.trans hb) ht)⟩
    let s:= p.erase i
    have hC (U : A → ℝ→ℂ) : walked U (glyphs f p)=U (f i)*walked U (glyphs f s) := by
      rw [show glyphs f p=X (f i)*glyphs f s from (Finset.mul_prod_erase p (fun i=> X (R:=ℂ) (f i)) hi).symm]; funext x; simp [walked]
    let B' := C*v^n
    let X:=walked U (glyphs f s); let Y:= walked V (glyphs f s)
    have hz' : 0 ≤ B' := by unfold B'; positivity
    have h₁ := zero_le_one.trans hv
    obtain ⟨h₂,h₃,h₄⟩:= Hc A B U V v t hv ht h s f (by unfold s; rw [Finset.card_erase_of_mem hi]; omega)
    rw [hC,hC, show U (f i)*X-V (f i)*Y=U (f i)*(X-Y)+(U (f i)-V (f i))*Y by ring]
    have hp : J*v*B' ≤ T*v^(n+1) := by
      have h : J*v*B'≥0 := by positivity
      unfold T B' at *; rw [pow_succ]; linarith only [h]
    have hp' (f : ℝ → ℂ) (H : smooth j f (J*v*B')) : smooth j f (T*v^(n+1)) := ⟨H.1,fun i a=> (H.2 i a).trans hp⟩
    have ht' : J*v*(B'*t)+J*(v*t)*B'=T*v^(n+1)*t := by unfold T B'; ring
    rw [← ht']; refine ⟨hp' _ (H _ _ _ _ h₁ hz' (h.east (f i)) h₂), hp' _ (H _ _ _ _ h₁ hz' (h.west (f i)) h₃), collars _ _ _ _ _ ?_ ?_⟩
    exact H _ _ _ _ h₁ (mul_nonneg hz' ht) (h.east (f i)) h₄
    exact H _ _ _ _ (mul_nonneg h₁ ht) hz' (h.bar (f i)) h₃

end

theorem poetry (j n : ℕ) : ∃ C : ℝ,1 ≤ C ∧ ∀ (A : Type) (U V : A → ℝ → ℂ),∀ c t,1 ≤ c → 0 ≤ t → OrderedAt U V j c t →
    ∀ P : Normal.poly A,totalDegree P ≤ n →
      smooth j (walked U P) (coin P * (C*c^n)) ∧ smooth j (walked V P) (coin P*(C*c^n)) ∧ smooth j (walked U P-walked V P) (coin P*(C*c^n*t)) := by
  obtain ⟨C,hC,Hc⟩:=plants j n
  refine ⟨C,hC,fun A U V c t hc ht h P hp =>?_⟩
  have hz : ContDiffAt ℝ j (walked U P) 0 := walks _ _ (fun i => (h.east i).1) _
  have hv : ContDiffAt ℝ j (walked V P) 0 := walks _ _ (fun i => (h.west i).1) _
  have he : ∀ i∈P.support,smooth j (walked U (monomial i 1)) (C*c^n) ∧ smooth j (walked V (monomial i 1)) (C*c^n) ∧ smooth j (walked U (monomial i 1) -walked V (monomial i 1)) (C*c^n*t) := by
    intro i hi; obtain ⟨a,ha⟩ := Common.letter i; rw [ha]; exact Hc A _ U V c t hc ht h Finset.univ a (by simpa using (MvPolynomial.le_totalDegree hi).trans hp)
  choose x hx using fun k : Fin (j+1) => register_link U j k.val (fun i => (h.east i).1) (Nat.le_of_lt_succ k.isLt)
  choose v hv' using fun k : Fin (j+1) => register_link V j k.val (fun i => (h.west i).1) (Nat.le_of_lt_succ k.isLt)
  have hF (F : poly A) (i : ℕ) (hi : i ≤ j) : slopeCap i (walked U F) 0=‖x ⟨i,Nat.lt_succ_of_le hi⟩ F‖ := by rw [hx]; exact norm_iteratedFDeriv_eq_norm_iteratedDeriv
  have hG (F : poly A) (i : ℕ) (hi : i ≤ j) : slopeCap i (walked V F) 0=‖v ⟨i,Nat.lt_succ_of_le hi⟩ F‖ := by rw [hv']; exact norm_iteratedFDeriv_eq_norm_iteratedDeriv
  have hZ (F : poly A) (i : ℕ) (hi : i ≤ j) : slopeCap i (walked U F-walked V F) 0= ‖(x ⟨i,Nat.lt_succ_of_le hi⟩-v ⟨i,Nat.lt_succ_of_le hi⟩) F‖ := by
    rw [LinearMap.sub_apply,hx,hv',← iteratedDeriv_sub (((walks U j (fun i => (h.east i).1) F).of_le <| by exact_mod_cast hi)) (((walks V j (fun i => (h.west i).1) F).of_le <| by exact_mod_cast hi))]; exact norm_iteratedFDeriv_eq_norm_iteratedDeriv
  refine ⟨⟨hz,fun i hi=>?_⟩,⟨hv,fun i hi=>?_⟩,⟨hz.sub hv,fun i hi=>?_⟩⟩
  · rw [hF P i hi]; exact to_basis _ _ fun x hx=> (hF (monomial x 1) _ hi).symm |>.trans_le ((he x hx).1.2 i hi)
  · rw [hG P i hi]; exact to_basis _ _ fun x hx=> (hG (monomial x 1) _ hi).symm |>.trans_le ((he x hx).2.1.2 i hi)
  · rw [hZ P i hi]; exact to_basis _ _ fun x hx=> (hZ (monomial x 1) _ hi).symm |>.trans_le ((he x hx).2.2.2 i hi)

-- Evaluate all radial Taylor orders then set h to 1, port linear for Lists
abbrev evaluate_ray {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V] (P : ℝ → V) (j : ℕ) := ∑ i∈Finset.range (j+1), ((i.factorial:ℝ)⁻¹) • iteratedDeriv i P 0


lemma total_probe (A : poly B) (F : B→ℝ→ℂ) (d : ℕ) (G : ℝ) (h : smooth d (walked F A) G) : ‖evaluate_ray (walked F A) d‖ ≤ (d+1:ℝ)*G := by
  apply (norm_sum_le ..).trans; rw [show (d+1:ℝ)*G=∑ _i∈Finset.range (d+1), G by simp]
  refine Finset.sum_le_sum fun i hi => ?_; rw [norm_smul]
  apply (mul_le_of_le_one_left (norm_nonneg _) ?_).trans; exact norm_iteratedFDeriv_eq_norm_iteratedDeriv.symm.trans_le (h.2 i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
  rw [norm_inv,Real.norm_natCast]; exact inv_le_one_of_one_le₀ (by exact_mod_cast (i.factorial_pos))

lemma net_probe {X Y : ℝ → ℂ} (n : ℕ) (h : ContDiffAt ℝ n X 0) (hp : ContDiffAt ℝ n Y 0) : evaluate_ray X n-evaluate_ray Y n=evaluate_ray (X-Y) n := by
  unfold evaluate_ray; rw [← Finset.sum_sub_distrib]; apply Finset.sum_congr rfl; intro i hi
  have hv := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [iteratedDeriv_sub (h.of_le <| by exact_mod_cast hv) (hp.of_le <| by exact_mod_cast hv), smul_sub]
lemma count_probe {X : ℝ → ℂ} (n : ℕ) (C : ℝ) (h : smooth n X C) : ‖evaluate_ray X n‖ ≤ (n+1:ℝ)*C := by
  let p:= MvPolynomial.X (0: Fin 1) (R:=ℂ)
  let F (_ : Fin 1) := X
  have he : walked F p=X := funext fun i=> aeval_X ..
  rw [← he]; exact total_probe _ _ _ _ (he ▸ h)
lemma costs_ray (n : ℕ) (X : A → ℝ → ℂ) (h : ∀ i,ContDiffAt ℝ n (X i) 0) :
    ∃ L : poly A →ₗ[ℂ] ℂ, ∀ P, L P=evaluate_ray (walked X P) n := by
  choose f hf using fun i : Fin (n+1) => register_link X _ i.val h (Nat.le_of_lt_succ i.isLt)
  refine ⟨∑ i : Fin (n+1),(((i.val.factorial:ℝ)⁻¹:ℝ):ℂ) • f i,fun P=>?_⟩
  rw [LinearMap.sum_apply,evaluate_ray,← Fin.sum_univ_eq_sum_range]; apply Finset.sum_congr rfl; intro i _; rw [LinearMap.smul_apply,hf];rfl
lemma trill {X Y : ℝ → ℂ} (n : ℕ) (h : ContDiffAt ℝ n X 0) (hp : ContDiffAt ℝ n Y 0) (hx : asym n (X-Y)) : evaluate_ray X n=evaluate_ray Y n := by
  let f i := (i.factorial:ℝ)⁻¹ • iteratedDeriv i X 0
  let g i := (i.factorial:ℝ)⁻¹ • iteratedDeriv i Y 0
  have ht : asym n (X-Dims n f) := taylor_data h
  have hu : asym n (Y-Dims n g) := taylor_data hp
  have he : asym n (Dims n (f-g)) := ((hx.sub ht).add hu).congr_left fun i => by
    rw [dims_sub]; simp only [Pi.sub_apply]; abel
  unfold evaluate_ray; exact Finset.sum_congr rfl fun i hi=> sub_eq_zero.mp (retreat n he i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))
lemma total_set {X : ℝ → ℂ} (n : ℕ) (h : ContDiffAt ℝ n X 0) (hv : ∃ f:ℕ→ℂ, X= Dims n f) : evaluate_ray X n=X 1 := by
  let f (i : ℕ):ℂ := (i.factorial:ℝ)⁻¹ • iteratedDeriv i X 0
  have he : X=Dims n f := decipher n _ _ hv ⟨_,rfl⟩ (taylor_data h)
  nth_rw 2 [he]; simp only [Dims,one_pow,one_smul]; rfl
end YM.Next.Rank.Spindle
