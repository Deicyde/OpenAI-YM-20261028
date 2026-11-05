import YM.RG08.Forms.Lines
import YM.RG08.Forms.Cot

/-!
# Simultaneous rent: pull every slot by possibly distinct cover kernels at post-block prices
or varying preblock powers. Use Δ line needn't depend on other legs. `beacon` can specify enough
geometry ONLY on nonzero coefficients of each respective stencil; e.g. canonical path choices.
Shares are per leg (also at root!).
-/
noncomputable section
namespace YM.RG08.Forms
open Pert.Bulk Packets Finset Function
open scoped BigOperators Topology ENNReal Classical
set_option autoImplicit false
variable {I J M : Type}{n:ℕ}

abbrev Cables (n:ℕ)(I J:Type):= Fin n → I→J→ℝ

def lighthouse (d:Ground I)(D:Ground J)(σ τ:ℝ) (E K:Cables n I J):Prop:=
  0≤σ ∧ 0≤τ ∧ (∀ i x y, 0≤E i x y) ∧ ∀ (i j:Fin n), i≠j → ∀ a b x y, K i a x≠0 → K j b y≠0 → τ*D.span x y ≤ σ*d.span a b + E i a x + E j b y

def street (E K:Cables n I J) (p:Fin n→ℝ):Prop:=∀ i, 0≤p i ∧
   (∀ x,∑' y,bill (K i x y) (E i x y) ≤ ENNReal.ofReal (p i)) ∧ (∀ y,∑' x,bill (K i x y) (E i x y) ≤ ENNReal.ofReal (p i))

lemma two {i j:Fin n}(h:i≠j)(p:Fin n→ℝ)(hp:∀ i,0 ≤ p i) : p i+p j ≤ ∑ i,p i:=by
 have hh : ∑ k ∈ ({i,j} : Finset (Fin n)), p k ≤ ∑ k, p k :=
   Finset.sum_le_sum_of_subset_of_nonneg (subset_univ _) (fun k _ _ => hp k)
 simpa [h] using hh

def design (K:Cables n I J)(x:Tape n I)(y:Tape n J):=∏ i,K i (x i) (y i)
variable {d:Ground I}{D:Ground J}{σ τ C:ℝ}{E K:Cables n I J}{F:Flake n I}{p:Fin n→ℝ}

theorem lighthouse.position (h:lighthouse d D σ τ E K){x:Tape n I}{y:Tape n J}(hxy:design K x y≠0):
   τ*D.radius y ≤ σ*d.radius x+∑ i,E i (x i) (y i) := by
 have hs:=h.2.1;have hx:=h.1
 have he:=h.2.2.1
 have hn (x:Tape n I)(y:Tape n J):0≤σ*d.radius x+∑ i,E i (x i) (y i):= add_nonneg (mul_nonneg hx (d.radius_nn _)) (sum_nonneg fun _ _=>he ..)
 rcases eq_or_lt_of_le hs with hT|hT
 · rw [←hT,zero_mul];exact hn x y
 have hp (j:Fin n):K j (x j) (y j)≠0:=Finset.prod_ne_zero_iff.mp hxy j (mem_univ j)
 suffices H:D.radius y ≤ (σ*d.radius x+∑ i,E i (x i) (y i))/τ by simpa [mul_comm] using (le_div_iff₀ hT).mp H
 apply D.radius_le _ (div_nonneg (hn x y) hT.le)
 intro i j
 rcases eq_or_ne i j with hc|hc
 · rw [hc,D.stay];exact div_nonneg (hn x y) hT.le
 rw [le_div_iff₀ hT,mul_comm]
 apply (h.2.2.2 i j hc (x i) (x j) (y i) (y j) (hp i) (hp j)).trans
 have H:=two hc (fun i=>E i (x i) (y i)) (fun _=>he ..)
 have H':=mul_le_mul_of_nonneg_left (d.le_radius x i j) hx
 nlinarith [H']

/-- No arity dependence in width; Γ comparisons may need distinct E or a reproof that
both stencils and their differences satisfy this width geometry. -/
def vat (K:Cables n I J) (F:Flake n I) (y:Tape n J)(x:Tape n I):= F x*design K x y

def raft (K:Cables n I J)(F:Flake n I): Flake n J:=fun y=>∑' x,vat K F y x

def tow (K:Cables n I J)(F:Flake n I):Flake n J:=bleach (raft K F)

def cable (E K:Cables n I J):=fun i (x:I)(y:J)=>bill (K i x y) (E i x y)

lemma beam_vat (h:lighthouse d D σ τ E K) (x:Tape n I)(y:Tape n J) :
  bill (vat K F y x) (τ*D.radius y) ≤ mark d σ F x * ∏ i,cable E K i (x i) (y i):=by
 by_cases hxy:design K x y=0
 · simp [vat,hxy,bill]
 unfold vat
 rw [show (∏ i,_) = bill (design K x y) (∑ i,E i (x i) (y i)) from ?_]
 · exact bill_mul _ _ _ _ _ (h.position hxy)
 exact (bill_products (fun i=>K i (x i) (y i)) (fun i=>E i (x i) (y i))).symm

lemma sum_hold_factor (i:Fin n)(z:J)(x:Tape n I):
   (∑' y:Tape n J, row (fun y=>∏ k,cable E K k (x k) (y k)) i z y) =
        cable E K i (x i) z * ∏ k∈univ.erase i,(∑' a,cable E K k (x k) a):=by
 let V (k:Fin n)(a:J):= if k=i ∧ a≠z then 0 else cable E K k (x k) a
 have he (y:Tape n J):row (fun y=>∏ k,cable E K k (x k) (y k)) i z y=∏ k,V k (y k):=by
  by_cases hf:y i=z
  · simp only [row,hf,if_true]
    apply prod_congr rfl; intro j _
    by_cases hh:j=i<;>simp [V,hh,hf]
  unfold row
  rw [if_neg hf,prod_eq_zero (i:=i) (mem_univ i) (by simp [V,hf])]
 simp_rw [he,all_Δ V,←Finset.mul_prod_erase _ (fun k=>∑' a,V k a) (mem_univ i)]
 congr 1
 · have h:(V i)=fun a=>if a=z then cable E K i (x i) a else 0:=by ext a;by_cases hh:a=z<;>simp [V,hh]
   rw [h];simp [tsum_ite_eq]
 apply Finset.prod_congr rfl;intro a ha
 simp [V,(Finset.mem_erase.mp ha).1]

lemma Ensign.incoming {f:Tape n I→ℝ≥0∞}{P:ℝ≥0∞}(h:Ensign f P)(i:Fin n)(g:I→ℝ≥0∞):
   (∑' x:Tape n I,f x*g (x i)) ≤ P*∑' a:I,g a:=by
 have he (x:Tape n I): f x*g (x i)=∑' a,row f i a x*g a:=by simp [row,ite_mul]
 calc
   (∑' x : Tape n I, f x * g (x i)) =
       ∑' x : Tape n I, ∑' a : I, row f i a x * g a := tsum_congr he
   _ = ∑' a : I, ∑' x : Tape n I, row f i a x * g a :=
     ENNReal.tsum_comm
   _ = ∑' a : I, (∑' x : Tape n I, row f i a x) * g a := by
     apply tsum_congr
     intro a
     exact ENNReal.tsum_mul_right
   _ ≤ ∑' a : I, P * g a := by
     apply ENNReal.tsum_le_tsum
     intro a
     exact mul_le_mul_left (h i a) _
   _ = P * ∑' a : I, g a := ENNReal.tsum_mul_left

lemma raft_major (h:lighthouse d D σ τ E K)(hk:street E K p)(hf:Held d σ C F)(_hC:0≤C):
 Ensign (fun y:Tape n J=>∑' x, bill (vat K F y x) (τ*D.radius y)) (ENNReal.ofReal C * ∏ i,ENNReal.ofReal (p i)):=by
 intro i z
 let T k:=ENNReal.ofReal (p k)
 let U x:= mark d σ F x
 calc
 _ ≤ ∑' y:Tape n J, ∑' x:Tape n I,U x * row (fun y=>∏ k,cable E K k (x k) (y k)) i z y:= by
       apply ENNReal.tsum_le_tsum
       intro y
       by_cases hh : y i = z
       · unfold row
         simp only [hh, if_true]
         exact ENNReal.tsum_le_tsum fun x => beam_vat h x y
       simp [row, hh]
 _ = ∑' x:Tape n I, U x * (cable E K i (x i) z * ∏ k∈univ.erase i,(∑' a,cable E K k (x k) a)):=by
       rw [ENNReal.tsum_comm];simp_rw [ENNReal.tsum_mul_left,sum_hold_factor]
 _ ≤ ∑' x:Tape n I,U x * (cable E K i (x i) z * ∏ k∈univ.erase i,T k):=by
       refine ENNReal.tsum_le_tsum fun x=>mul_le_mul_right (mul_le_mul_right (prod_le_prod' ?_) _) _
       intro k _;exact (hk k).2.1 _
 _ ≤ _:=by
       simp_rw [←mul_assoc,ENNReal.tsum_mul_right];rw [←Finset.mul_prod_erase _ T (mem_univ i),←mul_assoc]
       exact mul_le_mul_left (((ensign.mp hf).incoming i _).trans (mul_le_mul_right ((hk i).2.2 z) _)) _

private lemma earn_product (S:Finset (Fin n))(p:Fin n→ℝ)(hp:∀ i∈S,0≤p i) : ENNReal.ofReal (S.prod p)=(∏ i∈S,ENNReal.ofReal (p i)):=by
 induction S using Finset.induction_on with
 | empty=>simp
 | @insert i s hi ih=> rw [prod_insert hi,prod_insert hi,ENNReal.ofReal_mul (hp i (mem_insert_self ..)),ih (fun i hi=>hp i (mem_insert_of_mem hi))]
lemma Held.raft (hf:Held d σ C F)(hC:0≤C)(h:lighthouse d D σ τ E K)(hk:street E K p): Held D τ (C*∏ i,p i) (Forms.raft K F):=by
 rw [ensign,ENNReal.ofReal_mul hC,earn_product _ _ fun i _=>(hk i).1];exact (raft_major h hk hf hC).mono (fun _=>bill_tsum ..) le_rfl
lemma Held.tow (hf:Held d σ C F)(hC:0≤C)(h:lighthouse d D σ τ E K)(hk:street E K p): Held D τ (C*∏ i,p i) (Forms.tow K F):=(hf.raft hC h hk).bleach (mul_nonneg hC (Finset.prod_nonneg fun i _=>(hk i).1))
lemma raft_sum (hn:0<n)(hf:Held d σ C F)(hC:0≤C)(h:lighthouse d D σ τ E K)(hk:street E K p)(y:Tape n J) : Summable (fun x=>‖vat K F y x‖):=by
 have he:= ENNReal.ofReal_ne_top (r:=C*∏ i,p i)
 rw [ENNReal.ofReal_mul hC,earn_product _ _ fun i _=>(hk i).1] at he
 have hf := bill_ne_top (ne_top_of_le_ne_top he ((raft_major h hk hf hC).point hn y))
 exact (hf.mul_right (Real.exp (τ * D.radius y))⁻¹).congr fun i => by
   simp [Real.norm_eq_abs]
end YM.RG08.Forms
