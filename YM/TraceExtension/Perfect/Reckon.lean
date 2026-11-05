import YM.TraceExtension.Perfect.Plot

/-! # Unified forecast budget. pre-L on literacy rows. -/
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Perfect
open Function Filter Matrix Lattice Precision Laurent Stationary Bloch Exterior Tree RG Wilson Finset
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {c f:Side}{G:Gauge}
def palest (A: Matrix (Body 1 f) (Body 1 c) ℝ)(j:Lines G f 1)(i:Lines G c 1):= uniformM A (desk i) j
lemma pale_const (S:StepData c f)(j:Lines G f 1)(i:Lines G c 1): uniformM (Precision.mean S) (desk j) i=palest (mean S).transpose j i:=by
 unfold palest; rcases i with ⟨a,i,m⟩; rcases j with ⟨b,j,k⟩
 rw [show uniformM (mean S) (desk (b,j,k)) (a,i,m)=_ from gate_f _ (a,i) m (b,j) k, show uniformM _ _ _ =_ from gate_f (mean S).transpose (b,j) k (a,i) m]; simp only [transpose_apply]; by_cases h:m=k <;> simp [*,eq_comm]
lemma palest_price (V:Matrix (Body 1 f) (Body 1 c) ℝ)(j:Lines G f 1)(Q:Site c→ℕ)(a b r):
    sh (fun i:Lines G c 1=> Q i.1) a b r (palest V j)= sh (fun i:Body 1 c=> Q i.1) a b r (V (j.1,j.2.1)):=star_mesh V (j.1,j.2.1) j.2.2 Q _ _ _
lemma palest_sub (V W:Matrix (Body 1 f) (Body 1 c) ℝ)(j:Lines G f 1): palest (V-W) j = palest V j-palest W j:=by
 funext i; change ((V-W)*ᵥ parts G 1 (arm _ _ _ (desk i)) j.2.2) _=_; rw [Matrix.sub_mulVec]; rfl
lemma skin_total {A P Q:Matrix (Body 1 f) (Body 1 c) ℝ}(v: Site c →ℕ)(x:Site f)(a t L C)
    (h:Settle (fun y:Body 1 c=> v y.1) (fun y:Body 1 f=> separation y.1 x) A P Q a t L C): Settle (fun y:Lines G c 1=>v y.1) (arrange x) (palest A) (palest P) (palest Q) a t L C:=by
 refine ⟨fun j=>?_,fun j=> ?_,fun j=> ?_,fun j hj=> ?_⟩
 · rw [palest_price]; exact h.total (j.1,j.2.1)
 · rw [palest_price]; exact h.p (j.1,j.2.1)
 · rw [palest_price]; exact h.q (j.1,j.2.1)
 rw [← palest_sub,← palest_sub,palest_price]; exact h.near (j.1,j.2.1) hj
section box
variable {I H J W:Type}[Fintype I][Fintype H][Fintype J][Fintype W]
 {L C α:ℝ}{b:ℕ}
def doubling (A:I→H→ℝ)(B:J→W→ℝ) : I⊕J→H⊕W →ℝ:= Sum.elim (fun i=>Sum.elim (A i) 0) (fun j=>Sum.elim 0 (B j))
lemma dock (A:H→ℝ)(B D t c r): sh (Sum.elim B D) t c r (Sum.elim A (0:W→ℝ))=sh B t c r A:=by simp [sh,Fintype.sum_sum_type]
lemma doug (A:H→ℝ)(B D t c r): sh (Sum.elim D B) t c r (Sum.elim (0:W→ℝ) A)=sh B t c r A:=by simp [sh,Fintype.sum_sum_type]
lemma doubling_pay {A P Q:I→H→ℝ}{B S R:J→W→ℝ}(e:H→ℕ)(g:W→ℕ)(u:I→ℕ)(v:J→ℕ)(hL:0<L) {C':ℝ}
    (h:Settle e u A P Q α b L C)(hk:Settle g v B S R α b L C'): Settle (Sum.elim e g) (Sum.elim u v) (doubling A B) (doubling P S) (doubling Q R) α b L (max C C'):=by
 refine ⟨?_,?_,?_,?_⟩
 · rintro (i|i)
   · change _≤_*rush L (u i); rw [show doubling A B (Sum.inl i)=_ from rfl]; change sh _ _ _ _ (Sum.elim (A i) 0) ≤_; rw [dock]; exact (h.total i).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (rush_nn hL _))
   change sh _ _ _ _ (Sum.elim 0 (B i)) ≤_;rw [doug]; exact (hk.total i).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (rush_nn hL _))
 · rintro (i|i)
   · change sh _ _ _ _ (Sum.elim (P i) 0) ≤ _; rw [dock]; exact (h.p _).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
   change sh _ _ _ _ (Sum.elim 0 (S i)) ≤ _; rw [doug]; exact (hk.p _).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
 · rintro (i|i)
   · change sh _ _ _ _ (Sum.elim (Q i) 0) ≤ _; rw [dock]; exact (h.q _).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
   change sh _ _ _ _ (Sum.elim 0 (R i)) ≤ _; rw [doug]; exact (hk.q _).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
 rintro (i|i) hi
 · rw [show doubling A B (.inl i)-doubling P S (.inl i)-doubling Q R (.inl i)=Sum.elim (A i-P i-Q i) 0 from funext fun j=>by cases j<;> simp [doubling],dock]; exact (h.near _ hi).trans (mul_le_mul_of_nonneg_right (le_max_left ..) (by positivity))
 rw [show doubling A B (.inr i)-doubling P S (.inr i)-doubling Q R (.inr i)=Sum.elim (0:H→ℝ) (B i-S i-R i) from funext fun j=>by cases j<;> simp [doubling],doug]; exact (hk.near _ hi).trans (mul_le_mul_of_nonneg_right (le_max_right ..) (by positivity))
end box

variable {g:StepData c f}{p : Clip} {M:PathData G}
variable {F: Forest g.ratio}{ρ : Bid.Dir G c→AxisChart G F}
variable (T:Matrix (Body 1 f) (Body 1 c) ℝ)

def quilt (g:StepData c f)(T:Matrix (Body 1 f) (Body 1 c) ℝ): pairA G f→ pairA G c→ℝ:= doubling (palest T) (palest (Precision.mean g).transpose)

lemma knit (Z: Link G c→ Stationary.Joint G c f)(i:g.Choices)(x:pairA G f)(y:pairA G c)
   (h:g.patch.Branches g.kernel G)(he: Thaw Z 0)(hz:Z 0=1)(hp:Teller g i p M 1 (1:Stationary.Joint G c f))(hu:fderiv ℝ (fun x=> content (Z x).1) 0=uniformM T):
     fderiv ℝ (stampA g i Z) 0 (desk y) x=quilt g T x y:=by
 rw [dot_predict g M i h he hz hp,hu]
 cases x with
 | inl x=> cases y with
    | inl y=> rw [show ∀ y:Lines G c 1, (bite G c (desk (.inl y))).1=desk y from ?_]; rfl
              intro y; funext i; change desk (I:=pairA G c) (Sum.inl y) (Sum.inl i)= desk y i; simp [desk,Pi.single_apply]
    | inr y=> rw [show (bite G c (desk (Sum.inr y))).1=0 from funext (fun i=> by change desk (Sum.inr y) (Sum.inl i)=(0:Link G c) i; simp [desk]),map_zero]; rfl
 | inr x=> cases y with
    | inl y=> simp [desk,quilt,doubling]
    | inr y=> change ∑ i:Lines G c 1,_= palest _ x y; rw [sum_eq_single y]; rotate_left
              · intro b _ h; rw [show desk (I:=pairA G c) (Sum.inr y) (.inr b)= 0 from (by simp [desk,Pi.single_apply,h]),mul_zero]
              · simp
              rw [show desk (I:=pairA G c) (.inr y) (.inr y)= 1 from Pi.single_eq_same ..,mul_one,pale_const]
end YM.Trace.Perfect
