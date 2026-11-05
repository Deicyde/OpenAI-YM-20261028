import YM.WilsonBulk.Transit.Calls
import YM.WilsonBulk.Heat.Paid

set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Sheet
open scoped Classical Topology BigOperators ENNReal
open Equiv Filter Function Finset Lattice Pert.Bulk
variable {X Y : Type} {δ σ θ p q p' q' M M' K e : ℝ} {D : Rule X} {E : Rule Y} {n m k : ℕ}
  {d A B : Duct X Y} {U : Legs (Duct X Y) m} {u : Page X m}
  {C : Legs (Duct X Y) (n+1)} {R S : Fin (n+1)→ℝ} {P P' : Page X (n+1)}
lemma bullet (g : Geometry D E θ σ d) (h : ∀ i,AuditLine (C i) d (n+1) (R i) (S i))
    (hh : Within D θ M P) (hp : 0≤σ) (y : Y) : Summable fun x:Legs X (n+1)×Legs Y n=> metal C P (hitch y x.2) x.1 := by
  have hz := till g h P hh y
  have hb := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hz
  refine summable_from_receipt (w:=fun x:(Legs X (n+1)×Legs Y n)=> σ*run E y x.2) (fun _=> mul_nonneg hp (run_nonneg ..)) ?_
  rw [ENNReal.tsum_prod (f:=fun i j=> bill (metal C P (hitch y j) i) (σ*run E y j))]; exact hb
lemma carrier (g : Geometry D E θ σ d) (h : ∀ i, AuditLine (C i) d (n+1) (R i) (S i)) (he : Within D θ M P) (hp : 0≤σ) (y : Legs Y (n+1)) : Summable (metal C P y) := by
  refine legs_succ (fun y : Legs Y (n+1)=> Summable (metal C P y)) ?_ y
  intro j w; exact (bullet g h he hp j).prod_symm.prod_factor w
lemma rent_tele (g : Geometry D E θ σ d) (h : ∀ i, AuditLine (C i) d (n+1) (R i) (S i)) (he : Within D θ M P)
    (y : Y) : rent E σ (tele C P) 0 y ≤ ENNReal.ofReal (S 0*(∏ i:Fin n, crop R i)*M) := by
  rw [rent_head]; apply LE.le.trans (ENNReal.tsum_le_tsum (fun v=> bill_tsum ..)) ?_
  rw [ENNReal.tsum_comm]; exact till g h P he y
-- base change of account on arbitrary e; old Regular.pay_one suffices if identical stencils
lemma roll_account (e : Fin n≃ Fin k) (P : Page X k) (x : X) (i : Fin n) : rent D σ P (e i) x = rent D σ (escort e.symm P) i x := by
  unfold rent; rw [← (casesEquiv e (Equiv.refl X)).tsum_eq _]; apply tsum_congr; intro a
  have hx : casesEquiv e (Equiv.refl X) a=a ∘ e.symm := rfl
  rw [hx]; simp only [Function.comp_apply, e.symm_apply_apply, run_escort]; rfl

lemma toll_tele (g : Geometry D E θ σ d) (h : ∀ i, AuditLine (C i) d (n+1) (R i) (S i)) (he : Within D θ M P)
    (i : Fin (n+1)) (y : Y) : rent E σ (tele C P) i y ≤ ENNReal.ofReal (S i*(∏ v ∈ univ.erase i, R v)*M) := by
  let q := Equiv.swap i 0
  have hz : q 0=i := Equiv.swap_apply_right ..
  have hx : ∏ v ∈ univ.erase i,R v=∏ v:Fin n, crop (R ∘ q) v := by
    let f := Function.update R i 1
    have hL : ∏ v ∈ univ.erase i,R v=∏ v,f v := by
      rw [← prod_erase (f:=f) _ (update_self ..)]; exact prod_congr rfl fun j hj=> by simp [f,(mem_erase.mp hj).1]
    rw [hL,← Equiv.prod_comp q f,Fin.prod_univ_succ,hz,show f i=1 from update_self ..,one_mul]; refine prod_congr rfl fun v _=> ?_
    have hv : q v.succ≠i := hz ▸ q.injective.ne (Fin.succ_ne_zero _)
    simp [f,crop,hv]
  have h' : ∀ j, AuditLine ((C ∘ q) j) d (n+1) ((R ∘ q) j) ((S ∘ q) j) := fun j=> h (q j)
  calc
    _ = rent E σ (tele (C ∘ q) (escort q.symm P)) 0 y := by rw [teleport_escort,← roll_account q (tele C P) y 0,hz]
    _ ≤ ENNReal.ofReal ((S ∘ q) 0*(∏ i:Fin n,crop (R ∘ q) i)*M) := rent_tele g h' (he.reindex q.symm) y
    _ = _ := by rw [← hx,Function.comp_apply,hz]
lemma fare (g : Geometry D E θ σ d) (h : ∀ i, AuditLine (C i) d (n+1) (R i) (S i)) (he : Within D θ M P)
    (hb : ∀ i : Fin (n+1),S i*(∏ v∈univ.erase i,R v)*M≤p) : Within E σ p (tele C P) := by
  have hp : 0≤p:= (mul_nonneg (mul_nonneg (h 0).floor (prod_nonneg (fun i _ => (h i).height))) he.1).trans (hb 0)
  exact ⟨hp,fun i x=> (toll_tele g h he i x).trans (ENNReal.ofReal_le_ofReal (hb i))⟩
lemma fare_const (g : Geometry D E θ σ d) (h : ∀ i, AuditLine (C i) d (n+1) p q) (he : Within D θ M P) :
    Within E σ (q*p^n*M) (tele C P) := by
  have hv (i : Fin (n+1)) : (univ.erase i).card=n:= by rw [card_erase_of_mem (mem_univ i),card_univ,Fintype.card_fin]; omega
  exact fare g h he (fun i=> by rw [prod_const,hv i])
lemma tele_plus (g : Geometry D E θ σ d) (h : ∀ i, AuditLine (C i) d (n+1) (R i) (S i)) (he : Within D θ M P) (hh : Within D θ M' P')
    (hs : 0≤σ) : tele C (P+P')= tele C P+tele C P' := by
  ext1 v; unfold tele; rw [Pi.add_apply]; have h' x : metal C (P+P') v x = metal C P v x+metal C P' v x := mul_add ..
  simp_rw [tsum_congr h']; exact (carrier g h he hs v).tsum_add (carrier g h hh hs v)
lemma tele_scale (c : ℝ) : tele C (c • P)=c • tele C P := by
  ext1 v; unfold tele; rw [Pi.smul_apply, smul_eq_mul,← tsum_mul_left]; apply tsum_congr; intro x; exact mul_left_comm ..
lemma tele_sub (g : Geometry D E θ σ d) (h : ∀ i, AuditLine (C i) d (n+1) (R i) (S i)) (he : Within D θ M P) (hh : Within D θ M' P')
    (hs : 0≤σ) : tele C (P-P') = tele C P-tele C P' := by
  rw [sub_eq_add_neg,tele_plus g h he hh.neg hs, sub_eq_add_neg, show -P'= (-1:ℝ) • P' from by simp,tele_scale,neg_smul,one_smul] -- rewrites wrong

lemma tele_sub_line {v v' : Legs (Duct X Y) (n+1)} (g : Geometry D E θ σ d) (h : ∀ i, AuditLine (v i) d (n+1) (R i) (S i)) (hv : ∀ i, AuditLine (v' i) d (n+1) (R i) (S i)) (he : Within D θ M P)
    (hs : 0≤σ) (i : Fin (n+1)) (h' : ∀ j,j≠i→ v j=v' j) :
    tele v P-tele v' P=tele (Function.update v i (v i-v' i)) P := by
  ext1 x; rw [Pi.sub_apply]; unfold tele; rw [← (carrier g h he hs x).tsum_sub (carrier g hv he hs x)]
  refine tsum_congr fun z=> ?_
  unfold metal lot; rw [← sub_mul]; congr 1
  simp_rw [← mul_prod_erase (s:=univ) _ (mem_univ i), update_self,Pi.sub_apply,sub_mul]
  have hz : (∏ x'∈univ.erase i, Function.update v i (v i-v' i) x' (z x') (x x')) = ∏ x'∈univ.erase i, v x' (z x') (x x') := by
    apply prod_congr rfl; intro j hj; simp [(mem_erase.mp hj).1]
  rw [hz]; congr 2
  apply prod_congr rfl; intro j hj; rw [h' j (mem_erase.mp hj).1]
end YM.WilsonBulk.Sheet
