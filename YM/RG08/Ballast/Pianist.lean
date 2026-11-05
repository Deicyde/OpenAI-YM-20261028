import YM.RG08.Ballast.Ear

/-!
# Factor true differences with leg-length estimates for future repeated transfers

Integral/exponential width of remaining coefficients. Real result without
postponing equality to limit binders.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary Matrix
open scoped Topology ContDiff
variable {α β ι : Type} {r d : ℕ} {w w' C A B : ℝ} {m : Side}

def trill : List (Keys r) → Stitch r
  | [] => fun _ => []
  | a::l => update (trill l) a.1.succ (a.2 :: trill l a.1.succ)
lemma trill_count (b : List (Keys r)) : ∑ i,(trill b i).length=b.length := by
  induction b with
  | nil => simp [trill]
  | cons a b ih =>
    rw [← Finset.add_sum_erase univ _ (mem_univ a.1.succ),List.length_cons,← ih,← Finset.add_sum_erase univ (fun i => (trill b i).length) (mem_univ a.1.succ)]
    simp only [trill,update_self,List.length_cons]; rw [add_right_comm _ 1]; congr 2; exact sum_congr rfl fun i hi => by rw [update_of_ne (mem_erase.mp hi).1]
lemma trill_bound (b : Fin d → Keys r) (i) : (trill (List.ofFn b) i).length≤d :=
  (single_le_sum (f:=fun j=>(trill (List.ofFn b) j).length) (fun _ _=> Nat.zero_le _) (mem_univ i)).trans (by rw [trill_count, List.length_ofFn])
lemma trill_join (b : List (Keys r)) (w : Space r) : ∏ i, sparksZ (plotted w i) (trill b i)=(b.map fun i => divZ i w).prod := by
  induction b with
  | nil => simp [trill,sparksZ]
  | cons a b ih =>
    rw [← Finset.mul_prod_erase univ _ (mem_univ a.1.succ),List.map_cons,List.prod_cons,← ih,← Finset.mul_prod_erase univ (fun i => sparksZ (plotted w i) (trill b i)) (mem_univ a.1.succ)]; simp only [trill,update_self,sparksZ_cons]; rw [mul_assoc]; congr 1; congr 1; exact prod_congr rfl fun i hi => by rw [update_of_ne (mem_erase.mp hi).1]
lemma trill_fin_join (b : Fin d → Keys r) (w : Space r) : ∏ i, sparksZ (plotted w i) (trill (List.ofFn b) i) = ∏ i, divZ (b i) w := by
  rw [trill_join]
  induction d with
  | zero => simp
  | succ d ih => rw [Fin.prod_univ_succ]; simp only [List.ofFn_succ,List.map_cons,List.prod_cons,ih]

lemma finger_prize (v : Breed r α) {f : Shift (Keys r)→ℝ} (hf : Width w C f) (hw : 0≤w) : Glow (pool f (finger v)) w C := by
  apply Charge.poolage _ (ling_one hw); simpa only [Charge,Width,ling,finger_size] using hf

variable [Fintype α] [DecidableEq α]

def pedalled (F : Shale α (r+1)) (l : Stitch r) (v : Fin (r+1) → PAC α m) : ℝ :=
    recital F m (fun i => motion α m (l i) *ᵥ v i)
lemma pedal_axes (x : PAC α m) (l : List Axis) : axes (motion α m l *ᵥ x)=swingD l (axes x) := by
  induction l with
  | nil => rw [motion_zero,Matrix.one_mulVec]; rfl
  | cons i l ih =>
    rw [motion_walk,← Matrix.mulVec_mulVec,swingD,LinearMap.comp_apply, ← ih]
    ext1 a
    change ( ( (((knock α i).acts m *ᵥ (motion α m l *ᵥ x)) a):ℝ) :ℂ) = _ - _
    rw [knock_entry]; push_cast; rfl
lemma pedal_pin (l : Stitch r) {g : Shift (Keys r) → ℝ} (h : Width w C g) (hw : 0≤w) (b : Breed r α) (v : Fin (r+1) → PAC α m) :
    (pedalled (pool g (finger b)) l v:ℂ)=pinRing l (fun i => (g i:ℂ)) b m (axes ∘ v) := by
  have he : Width w C (fun i => (g i:ℂ)) := by simpa only [Width,Complex.norm_real] using h
  rw [pedalled,recital_pool _ (h.summable hw),pinRing_on _ _ _ he hw]
  simp_rw [Complex.ofReal_sum,Complex.ofReal_tsum]
  rw [Summable.tsum_finsetSum (fun i _ => pinRing_reach l (fun i => (g i:ℂ)) b he hw i _)]
  refine sum_congr rfl fun z _ => tsum_congr fun i => ?_
  rw [pinion_eval]; unfold rosary; push_cast; rw [mul_comm]; congr 1
  refine prod_congr rfl fun j _ => ?_
  exact congr_fun (pedal_axes (v j) (l j)) (silks z (finger b i) j)

variable {F : Shale α (r+1)}
abbrev Dolce (d : ℕ) (F : Shale α (r+1)) := ∀ i, Rays d (aria F i ∘ axes)
theorem sostenuto (α : Type) [Fintype α] [DecidableEq α] (r d : ℕ) {w} (hw : 0<w) :
    ∃ η K : ℝ, 0 < η ∧ η ≤ w ∧ 0 ≤ K ∧ ∀ {A : ℝ}, ∀ F : Shale α (r+1), Glow F w A →
        ordered F → Dolce d F → ∃ T : Breed r α → (Fin d → Keys r) → Shale α (r+1),
          (∀ i j, Glow (T i j) η (A*K)) ∧
          ∀ (m : Side) (v : Fin (r+1) → PAC α m), recital F m v = ∑ b : Breed r α,∑ j,pedalled (T b j) (trill (List.ofFn j)) v := by
  obtain ⟨η,K,hη,hθ,hK,H⟩ := real_difference_division (Keys r) d _ hw
  refine ⟨η,K,hη,hθ,hK,fun {A} F h he hp=>?_⟩
  have hs : Summable F := h.summable (ling_one hw.le)
  choose T hT hP using fun i => H A h.nonneg (F ∘ finger i) (finger_charge h i) (hp i)
  let g b j i := (T b j i:ℂ)
  have hg b j : Width η (A*K) (g b j) := by simpa only [Width,g,Complex.norm_real] using hT b j
  refine ⟨fun b j => pool (T b j) (finger b),fun i j => finger_prize i (hT i j) hη.le, fun m v => ?_⟩
  have hu : chorale F m = ∑ b : Breed r α,∑ j, pinRing (trill (List.ofFn j)) (g b j) b m := by
    apply relay_ext; intro p; simp only [_root_.sum_apply]; let k (i) := (p i).2; let P i := (p i).1
    rw [aria_shown F hs he P k]; change _=∑ b : Breed r α, ∑ j,pinRing _ _ _ _ (fun i => relay (P i) (k i))
    rw [sum_eq_single k]; swap
    · intro b _ hb; exact sum_eq_zero fun i _ => (pinRing_rec _ _ b (hg b i) hη.le P k).trans (if_neg fun h=>hb h.1)
    swap; · simp
    simp_rw [pinRing_rec (trill _) _ _ (hg k _) hη.le P k,show (aria F k (outphase P))=_ from hP _ _ (out_real P)]; split
    next ht => simp only [ht,true_and, ↓reduceIte, Finset.mul_sum]; unfold factorRay; simp_rw [trill_fin_join]; rfl
    next ht => simp [ht]
  apply Complex.ofReal_injective; rw [← chorale_real,hu,_root_.sum_apply,Complex.ofReal_sum]
  simp_rw [_root_.sum_apply,Complex.ofReal_sum]; apply sum_congr rfl; intro i _
  exact sum_congr rfl fun j _ => (pedal_pin _ (hT i j) hη.le i v).symm
end YM.RG08
