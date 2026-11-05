import YM.RG08.Ballast.Coda


set_option autoImplicit false
noncomputable section
namespace YM.RG08
open RG Laurent Lattice Wilson Bloch Next.Free Push.AbsoluteSums Finset Function Filter
open UVExt.Paths Stationary
-- avoid decidableeq mismatches below for finite coordinate indexing
open scoped Topology ContDiff
variable {α β ι : Type} {r : ℕ} {w w' C A B : ℝ} {m : Side}

def finger (v : Fin (r+1)→ α) (x : Shift (Keys r)) : Beads α (r+1) := fun j => (Fin.cons (α:=fun _=>Cover) 0 (fun i : Fin r => fun a:Axis => x (i,a)) j,v j)
lemma fingered (v : Fin (r+1)→α) : Injective (finger v) := by
  intro x y h; funext ⟨i,j⟩; exact congr_fun (congr_arg Prod.fst (congr_fun h i.succ)) j
lemma finger_back (v : Fin (r+1)→α) (b : Beads α (r+1)) (h : CenterDot b) (he : ∀ i,(b i).2=v i) :
    finger v (fun j : Keys r => (b j.1.succ).1 j.2)=b := by
  funext i; apply Prod.ext _ (he i).symm
  refine Fin.cases ?_ (fun j => ?_) i; exacts [Eq.symm (show (b 0).1=0 from h),rfl]
lemma finger_size (v : Fin (r+1)→α) (b : Shift (Keys r)) : girth (finger v b)=size b := by
  unfold girth; rw [Fin.sum_univ_succ]; unfold finger; simp only [Fin.cons_zero, Fin.cons_succ]
  simp [size,Fintype.sum_prod_type]

lemma finger_charge {F : Shale α (r+1)} (h : Glow F w C) (v : Fin (r+1)→α) : Width w C (F ∘ finger v) := by
  have he := budget_pull (finger v) (fingered v) h
  simpa only [Width, Function.comp_apply,ling,finger_size] using he

-- using phase rather than exponent variables
def aria (F : Shale α (r+1)) (v : Fin (r+1)→α) := Laurent.read (fun j => (F (finger v j):ℂ))
lemma aria_paid {F : Shale α (r+1)} (h : Glow F w A) (hw : 0 < w) (v) : Firm w A (aria F v) :=
  Firm.of_series (by simpa only [Width,comp_apply,Complex.norm_real] using finger_charge h v) hw

section cast
variable [Fintype α] [DecidableEq α] {F H : Shale α r}
-- prove using recording/pool applying on finite periods, colored version too.
def chorale (K : Shale α r) (m : Side) : RecordM ℂ (Fin r) (Co m α) :=
  enlarge (recital K m).toMultilinearMap
private def swung (K : Shale α r) (m : Side) : RecordM ℂ (Fin r) (Co m α) := ∑ z,
    recording (fun i => ((pool K (silks (m:=m) z) i):ℂ))
lemma chorale_read (K : Shale α r) (h : Summable K) (m : Side) (v : Fin r→Phase (Co m α)) :
    chorale K m v = ∑ z,∑' j,(K j:ℂ)*(∏ i, v i (silks z j i)) := by
  have hu : chorale K m=swung K m := enlarge_unique _ _ (fun b => by
    rw [chorale,enlarge_real]; unfold recital swung
    simp only [_root_.sum_apply,recording_apply, ContinuousMultilinearMap.coe_coe]
    push_cast; apply Finset.sum_congr rfl; intro i _
    change ((recording (pool K (silks i)) b):ℂ)=_; rw [recording_apply]; push_cast; rfl)
  rw [hu,swung,_root_.sum_apply]; apply Finset.sum_congr rfl; intro z _
  rw [recording_apply]
  let f (i : Fin r → Co m α) := ∏ k, v k (i k)
  have hs : Summable (fun i=> (K i • f (silks z i))) := by
    apply Summable.of_norm; apply Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> ?_) (h.norm.mul_right (∏ i,‖v i‖))
    rw [norm_smul]; exact mul_le_mul_of_nonneg_left ((norm_prod ..).le.trans (prod_le_prod (fun _ _=>norm_nonneg _) (fun k _=>norm_le_pi_norm (v k) _))) (norm_nonneg _)
  have hv := (pool_read K f (silks z) h hs).tsum_eq; rw [tsum_fintype] at hv; simp only [Complex.real_smul,f] at hv
  refine Eq.trans (sum_congr rfl fun i _ => mul_comm ..) hv

lemma chorale_real (K : Shale α r) (m : Side) (v : Fin r → PAC α m) :
    chorale K m (axes ∘ v)=(recital K m v:ℂ) := enlarge_real ..
omit [DecidableEq α] in
lemma choir_money (K : Shale α r) (h : Summable K) (m : Side) (v : Fin r → Phase (Co m α)) (z) :
    Summable (fun j => (K j:ℂ)*(∏ i, v i (silks z j i))) := by
  apply Summable.of_norm; apply Summable.of_nonneg_of_le (fun _=> norm_nonneg _) (fun i=> ?_) (h.norm.mul_right (∏ i,‖v i‖))
  rw [norm_mul,Complex.norm_real]; exact mul_le_mul_of_nonneg_left ((norm_prod ..).le.trans (prod_le_prod (fun _ _=>norm_nonneg _) (fun k _=>norm_le_pi_norm (v k) _))) (norm_nonneg _)

lemma cells_plural (v : ι→Site m) (s : Finset ι) (z : Site m) : (∏ i∈s,cell (v i) z)=cell (∑ i∈s,v i) z := by
  classical
  induction s using Finset.induction with
  | empty => simp [cell]
  | insert i t hi ih => rw [prod_insert hi,sum_insert hi,ih,cell_duality (_+_),cell_add,cell_duality z,cell_duality z]

omit [Fintype α] in
lemma nut_cell (p : Fin (r+1) → Site m) (v : Fin (r+1)→α) (z) (x : Shift (Keys r)) :
    (∏ i,relay (p i) (v i) (silks z (finger v x) i)) = cell (∑ i,p i) z * mode (outphase p) x := by
  unfold relay tune silks
  simp only [finger,Pi.single_eq_same,mul_one,cell_add, Finset.prod_mul_distrib, cells_plural]; congr 1
  rw [Fin.prod_univ_succ]; simp only [Fin.cons_zero, Fin.cons_succ,cell_wrap, mode_zero,one_mul]
  unfold mode; rw [Fintype.sum_prod_type (f:=fun i : Fin r × Axis => outphase p i*(x i)),mul_sum, Complex.exp_sum]; rfl


lemma aria_shown (K : Shale α (r+1)) (h : Summable K) (hg : ordered K) (p : Fin (r+1)→ Site m) (v : Fin (r+1)→α) :
    chorale K m (fun i => relay (p i) (v i))=if ∑ i,p i=0 then
        (Fintype.card (Site m) :ℂ)*aria K v (outphase p) else 0 := by
  rw [chorale_read K h]
  have he (z : Site m) : ∑' j,(K j:ℂ)*(∏ i,relay (p i) (v i) (silks z j i))=cell (∑ i,p i) z*aria K v (outphase p) := by
    rw [← (fingered v).tsum_eq]
    · unfold aria Laurent.read; rw [← tsum_mul_left]; apply tsum_congr; intro b
      rw [nut_cell p v z b]; simp only [smul_eq_mul]; ring
    intro b hb
    have hu (i) : (b i).2=v i := by
      by_contra hy; apply hb
      change (K b:ℂ)*_=0; rw [prod_eq_zero (mem_univ i) ?_,mul_zero]; unfold relay tune; simp only [silks,Pi.single_eq_of_ne hy,mul_zero]
    refine ⟨_,finger_back v b (hg b fun hv=>hb ?_) hu⟩
    simp [hv]
  simp_rw [he,← sum_mul]; split
  next he => simp [he,cell]
  next he => rw [sum_cell he,zero_mul]
end cast

variable {G : Gauge} {V : Link G m→ℝ}
def gallery (F : Shale (Loc G 1) (r+1)) : Picture G r := fun i b => aria F (fun j => (b j,i j))
lemma gallery_funds {F : Shale (Loc G 1) (r+1)} (h : Glow F w A) (hw : 0<w) (i b) : Firm w A (gallery F i b) := aria_paid h hw _
lemma gallery_marks {F : Shale (Loc G 1) (r+1)} (h : Tunable F) (he : Tensor.coeff V (r+1) 0=recital F m) :
    Recorded (gallery F) V 0 := by
  refine (record_exact ..).2 fun p i b => ?_
  rw [note_map,he]; exact aria_shown F h.1 h.2.1 p (fun j => (b j,i j))
end YM.RG08
