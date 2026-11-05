import YM.OPE.Columns.SectorCost
import YM.MergeProof.East.Gran

/-!
# Keep the engineering and reference coordinates of the weak stations

Calibrate at the cutoff with the very same matrices as the station (not with
an independent choice of field trajectory). Units paid at a common level k,
where the actual measured radius and the spacing agree to subpowers. No
fixed-log strengthening available from the naked post-block prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Levy
open Set Filter Function Extraction RG MergeProof Wilson Labels Columns Spec Table
open Next Next.Rank Next.Rank.Price Next.UVStress Bid Source Next.Extract Dash Work.G08
open Next.Rank.East Climb Further.CorrectedLift
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge} (C:Family G) {d k N p:ℕ}
local notation "A" => C.path.levels
local notation "T" => C.S.scale

lemma station_monitor (h:G.Simple)(b:ℝ): RateLE atTop T (Rank.Station.mag A b) 0 :=by
   let K:= (A).clock
   let Y:= K.hatBeta
   have ht:= C.S.divergent
   have hb: RateLE atTop T Y 0:=by
     have hi : RateLE atTop T T 0:=by
       intro r hr; filter_upwards [ht.eventually_ge_atTop 0, ht.eventually_ge_atTop (8*(r^2)⁻¹)] with i hi he
       -- exp >= x^2/4
       have hr': 0<r^2:=sq_pos_of_pos hr
       rw [Real.norm_eq_abs,abs_of_nonneg hi]
       refine le_trans (show T i ≤ (r*T i/2)^2 from by
         have h':=(inv_mul_le_iff₀ hr').mp (show (r^2)⁻¹*8 ≤ T i from (mul_comm ..).trans_le he)
         have hy:=mul_le_mul_of_nonneg_right h' hi
         nlinarith only [hi,hy]) ?_
       have hx:= Real.add_one_le_exp (r*T i/2)
       rw [show Real.exp (r*T i)=Real.exp (r*T i/2)^2 from by rw [← show r*T i/2 + r*T i/2=r*T i from by ring,Real.exp_add]; rw [show (r*T i/2 + r*T i/2)/2 = r*T i/2 from by ring, pow_two]]
       exact pow_le_pow_left₀ (show 0 ≤ r*T i/2 from div_nonneg (mul_nonneg hr.le hi) (by norm_num)) (by linarith only [hx]) 2
     have hp:= (RateLE.const G.slopeConstant ht).mul hi; rw [zero_add] at hp
     have hp:= (RateLE.const (K.bar) ht).add hp ht
     exact hp
   have he:∀ᶠ k in atTop, Rank.Station.mag A b k ≤ Y k :=
     ((Rank.Station.hat_rate A h).eventually (Vac.Numbers.cost b 1 zero_lt_one)).mono fun k hk=>by
        rw [Real.rpow_one] at hk; exact hk
   apply hb.transfer (he.mono fun i hi=>(Real.norm_of_nonneg (Rank.Station.mag_pos ..).le).le.trans (hi.trans (Real.le_norm_self _)))

-- Names of namespaces shadow each other. Check builds.
variable (d k)
def preExpense (b:ℝ):ℝ:= pre_billing
where
 pre_billing:= let ρ := Rank.Station.mag C.path.levels b k
               let r:= 2*C.path.levels.clock.monitor k
               2*∑ i, ‖(r ^ ((C.labels.level d).grades i).2 : ℝ) * (ρ ^ ((C.labels.level d).grades i).1:ℝ)‖
def signal (b:ℝ) := (C.S.a k)^d * preExpense C d k b

private lemma size_sc (P:Labels.Frame G d) (g:P.Coeff)(x:ℂ):P.coeffSize (x•g) = ‖x‖*P.coeffSize g:=by
   unfold Labels.Frame.coeffSize; simp only [Pi.smul_apply,norm_smul,Finset.mul_sum]

include C
lemma quotation {b:ℝ}(h:C.Makes)(hr:C.ref d≤k)(hk:k≤N)(P:Module.End ℂ (C.label d)) (ht:Price.Tested C d k N p P)(x:C.label d) :
   let μ:=Rank.Station.mag A b k
   let z:=ladd C μ k N p d P x
   quota C d k N p z ≤ signal C d k b * ‖x‖ := by
     intro μ z
     let L:=C.labels.level d; let t:= shrink C k N p; let v:=weightTag C d μ x
     have ht':0 < t := shrink_pos C h hk p; let r:=2*C.path.levels.clock.monitor k; have hz:t⁻¹ ≤ r:= shrink_min C h hk p
     have hQ: L.scaled t (P z)=v:= poured h hr hk μ P ht x
     have hB: P z=L.scaled t⁻¹ v:=by have he:=L.scaled_inv (inv_ne_zero ht'.ne') (P z); rw [inv_inv,hQ] at he; exact he.symm
     have he:L.coeffSize (P z) ≤ L.coeffSize (L.scaled r v):=by
         unfold Frame.coeffSize
         apply Finset.sum_le_sum
         intro i hi
         rw [hB,Frame.scaled_apply,Frame.scaled_apply,norm_mul,norm_mul,Complex.norm_real,Complex.norm_real]; refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
         rw [Real.norm_of_nonneg (pow_nonneg (inv_pos.mpr ht').le _),Real.norm_of_nonneg (pow_nonneg ((inv_pos.mpr ht').le.trans hz) _)]; exact pow_le_pow_left₀ (inv_pos.mpr ht').le hz _
     have e_i:= (ht.cost C P z).trans (mul_le_mul_of_nonneg_left he zero_le_two)
     have h0: quota C d k N p z = (C.S.a k)^d * L.coeffSize (awake C d k N p z):=by
       unfold Price.awake; rw [size_sc,norm_inv,Complex.norm_pow,Complex.norm_real,Real.norm_of_nonneg (C.S.a_pos _).le,←mul_assoc,mul_inv_cancel₀ (pow_ne_zero _ (C.S.a_pos _).ne'),one_mul]; rfl
     unfold signal preExpense preExpense.pre_billing
     rw [h0,mul_assoc]
     apply mul_le_mul_of_nonneg_left (le_trans e_i ?_) (pow_nonneg (C.S.a_pos _).le _)
     rw [mul_assoc,Finset.sum_mul]
     apply mul_le_mul_of_nonneg_left (_:L.coeffSize (L.scaled r v) ≤ _) zero_le_two
     change (∑ i:L.Index,_) ≤ _
     apply Finset.sum_le_sum
     intro j hj
     rw [Labels.Frame.scaled_apply,norm_mul]
     change ‖(↑(r^(L.grades j).2):ℂ)‖ * ‖(↑μ:ℂ)^(L.grades j).1 * x j‖ ≤ _
     simp only [norm_mul,norm_pow,Complex.norm_real]; rw [←mul_assoc, ← norm_mul]
     exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x _) (mul_nonneg (pow_nonneg (norm_nonneg _) _) (pow_nonneg (norm_nonneg _) _))

variable {k}
lemma signal_rate (b:ℝ)(hG:G.Simple):RateLE atTop T (fun k=>signal C d k b) (-(d:ℝ)) :=by
    have hx:RateLE atTop T (fun i=>(A).clock.monitor i) 0:= by exact (station_monitor C hG 1).congr (Eventually.of_forall fun i=> Real.rpow_one _)
    have ht:=C.S.divergent
    let w(k:ℕ):=2*(A).clock.monitor k
    let v(k:ℕ):=Rank.Station.mag A b k
    have hw:RateLE atTop T w 0:=by simpa only [zero_add] using (RateLE.const (2:ℝ) ht).mul hx
    have hv:=station_monitor C hG b
    have he : RateLE atTop T (fun k:ℕ=>∑ i, ‖w k ^ ((C.labels.level d).grades i).2 * v k ^ ((C.labels.level d).grades i).1‖) 0:=RateLE.sum ht (fun i _=>by
      simpa only [mul_zero,zero_add] using ((hw.pow ((C.labels.level d).grades i).2 ht).mul (hv.pow ((C.labels.level d).grades i).1 ht)).norm)
    have he0:= (RateLE.const (2:ℝ) ht).mul he
    have hs:RateIs atTop T C.S.a (-1:ℝ):=⟨Eventually.of_forall C.S.a_pos, (Ribbons.Note.note_a C.S).pitch⟩
    simpa [signal,preExpense,preExpense.pre_billing, w,v] using ((hs.pays ht).pow d ht).mul he0

end YM.OPE.Levy
