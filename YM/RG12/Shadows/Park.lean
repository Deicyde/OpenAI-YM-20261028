import YM.RG12.Shadows.Bath
/-! Scaled derivative holds. Retain powers per order. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG12.Shadows
open Set Metric Filter Function ConnectedActivityE6 ConnectedActivityE6.Blaze Tablet PhysicalNext.Repeat.Prism
open scoped ContDiff Topology BigOperators Classical
namespace Charges
variable {R:Haze}{p:ℝ}{X N D:ℕ→ℝ}(hN: Charges R 0 N)(hX:Charges R 0 X)
lemma holdMul (hD:Charges R p D)(hN:Charges R 0 N):Charges R p (fun x=> N x*D x):= by simpa only [zero_add] using hN.mul hD
lemma holdRight (hD:Charges R p D)(hN:Charges R 0 N):Charges R p (fun x=> D x*N x):= by simpa only [add_zero] using hD.mul hN
include hN hX
lemma banner_charge (n:ℕ):Charges R 0 (fun i=>banner (X i) (N i) n):=by
   unfold banner token; refine Charges.right ?_ _
   suffices h:∀ S:Finset ℕ,Charges R 0 (fun i=>∑ j∈S,(N i*X i*(N i*X i)+1)^j*(N i*X i)) from h _
   intro S; induction S using Finset.induction_on with
   | empty=>simpa using! frozen 0 R
   | insert i s hi ih=>
     have h:= holdMul hX hN; simp_rw [Finset.sum_insert hi]; exact Charges.add (holdMul h (((holdMul h h).add (frozen 1 _)).raise _ rfl)) ih
lemma reck_charged {n:ℕ}(A:Anthem n):Charges R 0 (fun i=>reck A (N i) (X i)):=by
   have hf:Charges R 0 (fun i=> freight n (N i) (X i) (X i)):=by unfold freight; exact right (holdMul (holdMul hX hX) hN) _
   have ht:Charges R 0 (fun i=> tally0 n (N i) (X i)):=by
      unfold tally0; apply holdRight (((add (frozen 1 R) hN).raise n rfl).left _); exact (((add (frozen 1 R) (add hf (frozen 1 R))).raise n rfl).left _)
   unfold reck; exact left ((add (frozen 1 R) (right (add (frozen 1 R) ht) _)).raise n rfl) _
lemma costes {n:ℕ}(hD:Charges R p D):Charges R p (fun i=> gear (D i) (X i) (N i) n)∧Charges R p (fun i=> sail (D i) (X i) (N i) n)∧Charges R p (fun i=> revs (D i) (X i) (N i) n):=by
   have h:= banner_charge hN hX n; have hh : Charges R p (fun i=> hoop (D i) (X i) (N i) n):= by unfold hoop freight; exact right (holdMul (holdRight hD h) hN) _
   have hv :Charges R p (fun i=> gear (D i) (X i) (N i) n) := holdMul hh (hN.raise 2 rfl)
   refine ⟨hv,holdRight (holdMul hv hN) (((frozen 1 _).add hN).raise n rfl),?_⟩
   unfold revs freight; exact right (holdMul (holdMul hh h) hN) _
end Charges
variable {R:Haze}{I E J:ℕ→Type}[∀ i,Fintype (J i)][∀ i,DecidableEq (J i)][∀ i, NormedAddCommGroup (E i)][∀ i,NormedSpace ℝ (E i)]
abbrev Circle (J:ℕ→Type):= fun i=>J i × J i
abbrev Gram (J E:ℕ→Type):=∀ i:ℕ,E i→Matrix (J i) (J i) ℝ
def gaze (B:Gram J E):Drift (Circle J) E:= fun i j x=> B i x j.1 j.2
def birth (B:Gram J E):= fun i (j:Circle J i)=> B i 0 j.1 j.2
def dusk (B:Gram J E):= fun i x=> (B i x)⁻¹
def light (R:Haze) i:= Real.exp (-R.H i)
lemma powers (R:Haze): Charges R 1 (light R) ∧Charges R (-1) (fun i=>(light R i)⁻¹)∧∀ i, 0<light R i:=by
   have h (n:ℝ):Charges R (-n) (fun i=>Real.exp (n*R.H i)):=by unfold Charges; rw [neg_neg]; exact OPE.RateLE.exp n R.warmth
   have hf:=h (-1); have hv:=h 1; rw [neg_neg] at hf; simp only [neg_one_mul] at hf; simp only [one_mul] at hv; unfold light; rw [show (fun i=>(Real.exp (-_) )⁻¹)=_ from ?_]; exact ⟨hf,hv,fun _=>Real.exp_pos _⟩ -- inference
   funext i; rw [←Real.exp_neg,neg_neg]
abbrev flick (f:Drift I E)(s:ℕ→ℝ):Drift I E:= fun i j y=> f i j ((s i) • y)
variable {p q:ℝ}{n:ℕ}{B:ℕ→ℝ}{u:Drift I E}
lemma lights_scale (H:Flares R n p u)(hh:Smooths n u)(hK: Charges R q B): Flares R n (p+n*q) (flick u B):=by
   obtain ⟨t,ha,ht⟩:=H.assumes; refine Flares.mk (ha.mul (hK.absolute.power n)) ?_
   filter_upwards [hh,ht] with i hi ht j; unfold normJ flick; rw [iter_scale _ _ (hi j),norm_smul, Real.norm_eq_abs,abs_pow,mul_comm]
   exact mul_le_mul_of_nonneg_right (ht j) (pow_nonneg (abs_nonneg _) _)
lemma click (h:Call R 2 p u):Sleeve R p p p u:=by
   obtain ⟨v,hd,hb⟩:=h
   have he (n:ℕ)(hn:n≤2):Flares R n p u:=by apply Flares.mk hd; filter_upwards [hb] with i hb j; have h:= (hb j).order n hn; rwa [one_pow,mul_one] at h
   exact ⟨hb.mono fun _ hi j=> (hi j).smooth, he _ (by decide),he _ (by decide), he _ (by decide)⟩
lemma scaled (H:Sleeve R 0 1 2 u) : Call R 2 0 (flick u (fun i=> (light R i)⁻¹)):=by
  obtain ⟨hK,hL,ht⟩:= powers R; let s i:=(light R i)⁻¹
  have hs:Sleeve R 0 0 0 (flick u s):=by
    refine ⟨?_,?_,?_,?_⟩
    · filter_upwards [H.smooth] with i hi j; unfold flick; exact (show ContDiffAt ℝ _ _ (s i • (0:E i)) from by simpa using! hi j).comp _ (contDiffAt_const.smul contDiffAt_id)
    · simpa only [Nat.cast_zero,zero_mul,add_zero] using! lights_scale H.zero (H.smooth.mono (by decide)) hL
    · simpa only [Nat.cast_one,one_mul,add_neg_cancel] using! lights_scale H.first (H.smooth.mono (by decide)) hL
    have he:= lights_scale H.second H.smooth hL; rw [show (2:ℝ)+(↑(2:ℕ):ℝ)*(-1)=0 by norm_num] at he; exact he
  exact hs.call le_rfl le_rfl le_rfl
lemma unscaled (H:Call R 2 0 (flick u (fun i=>(light R i)⁻¹))): Sleeve R 0 1 2 u:=by
  obtain ⟨hK,hL,ht⟩:=powers R; have H:= click H
  let t i:=(light R i)⁻¹; let v:=flick u t
  have hv: Sleeve R 0 1 2 (flick v (light R)):=by
     refine ⟨?_,?_,?_,?_⟩
     · filter_upwards [H.smooth] with i hi j; exact (show ContDiffAt ℝ _ _ (light R i • (0:E i)) from by simpa using! hi j).comp _ (contDiffAt_const.smul contDiffAt_id)
     · simpa only [Nat.cast_zero,zero_mul,add_zero] using! lights_scale H.zero (H.smooth.mono (m:=0) (by decide)) hK
     · simpa only [Nat.cast_one,one_mul,zero_add] using! lights_scale H.first (H.smooth.mono (m:=1) (by decide)) hK
     simpa using! lights_scale H.second H.smooth hK
  convert! hv using 1; ext i j y; unfold flick v flick t; rw [smul_smul,inv_mul_cancel₀ (ht i).ne',one_smul]
end YM.RG12.Shadows
