import YM.RemainderComparison.Flues.Kettle

/-!
# Pay a flue after shrinking and return ratings before more attachments
-/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Flues
open Function Filter Lattice Wilson RG Pressure Push Push.AbsoluteSums Finset Lyric Next.Scheduling AnalyticBridge.VerifiedReset
open ConnectedActivityE6 Coat PhysicalNext.Repeat
open scoped Topology BigOperators Classical
variable {G:Gauge}{L : Side} {x : ℝ} {σ r : ℝ}
local notation "A" => unitK
local notation "Q" => radiusB
local notation "F" => (fun x=> betaF G x L)

lemma cheap (x:ℝ): 0 < unitK x∧ unitK x≤1 := ⟨Real.exp_pos _,Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.rpow_nonneg (show 0 ≤ Vac.Numbers.P x from Real.exp_nonneg _) _))⟩
lemma buying (z:ℝ→ℝ)(hZ: ∀ᶠ x:ℝ in atTop, 0< z x ∧ z x ≤ 1) (v d:ℝ→ℝ)(hv:Rate G L r v)(hr:r<0)(hd:Rate G L 0 d)(hσ:0≤ σ)(k s:ℕ): ∀ᶠ x in atTop, ∀ β,inBand (betaF G x L) β→∃ w t γ, Resonant (radiusB x) k |v x| (z x*gStep β^(s+1)) |d x| σ (z x*gStep β^s) w t γ:=by
   let M x:ℝ:= ((Q x:ℝ)+(Q x:ℝ)+1)^4
   have hM(x):1 ≤ M x:= one_le_pow₀ (le_add_of_nonneg_left (by positivity))
   let D x := 4*(1+|d x|); have hD x:1 ≤ D x:=by have hp:=abs_nonneg (d x); unfold D; linarith
   let c x:=D x*M x; have hc x:1 ≤ c x:= one_le_mul_of_one_le_of_one_le (hD x) (hM x)
   have ht: Rate G L 0 M:=by unfold M; simpa only [zero_mul] using! ((((Rate.radius_price (G:=G) (L:=L)).add Rate.radius_price).add (Rate.const _)).pow 4)
   have hT: Rate G L 0 c:=by simpa only [zero_add] using! (((Rate.const 1).add (Brim.absolut hd)).mul_left 4).mul ht
   have hg:= Access.rates_apron (G:=G) (L:=L); let g:= Access.apron G L
   have hP:= Access.wide (Rate.const (G:=G) (L:=L) 1)
   have hV:= ((hv.mul ht).mul_left 8).below (by linarith) 1 zero_lt_one
   have hF:= (((hg.pow (s+1)).mul ht).mul_right 4).below (by push_cast; linarith) 1 zero_lt_one
   let ψ:=Real.exp 1
   have hx':0<ψ:=Real.exp_pos _
   have hK:= (((((hT.pow k).mul hg).mul ht).mul_right 4).mul_right ψ).below (by norm_num) 1 zero_lt_one
   filter_upwards [hZ,hP,hV,hF,hK] with x hzz hP hV hF hK β hβ
   let γ:= (M x)⁻¹
   have hm : 0 < M x:=zero_lt_one.trans_le (hM x); have hz : 0 < γ:= inv_pos.mpr hm
   let p:=z x; let y:= gStep β; let w:= p*y^(s+1)* M x*4
   obtain ⟨ht,he⟩:= hP.2 β hβ; have hy : 0 < y:= ht
   have hp: 0 < p:= hzz.1; have hw :0<w:=by unfold w; positivity
   have hi:1≤ c x:=hc x; have hu:γ≤1:=by unfold γ; exact inv_le_one_of_one_le₀ (hM x)
   have ha : |v x| ≤ γ/8:=by
      simp only [abs_mul,abs_of_pos hm,abs_of_pos (by norm_num : (0:ℝ)<8)] at hV
      unfold γ; field_simp; linarith
   refine ⟨w,c x,γ,⟨hw, ?_,hi,hσ,by linarith, ?_, ?_, ?_⟩⟩
   · apply le_trans ?_ ((le_abs_self _).trans hF); change p* y^(s+1) * M x *4 ≤ Access.apron G L x^(s+1)*M x*4
     gcongr; exact (mul_le_of_le_one_left (by positivity) (hzz.2)).trans (pow_le_pow_left₀ hy.le he.le _)
   · have hl : w⁻¹*(p*y^(s+1))=γ/4:=by unfold w γ; field_simp
     have hb : (c x)⁻¹* |d x| ≤ γ/4:=by unfold γ c D; rw [inv_mul_eq_div]; field_simp; linarith [abs_nonneg (d x)]
     change w⁻¹*(p*y^(s+1)) + _ ≤ _; rw [hl]; linarith only [hz,hb,ha]
   · push_cast; rw [show _^4 *γ = M x *(M x)⁻¹ from rfl, mul_inv_cancel₀ hm.ne']
   change c x^k*w*(Real.exp γ - 1) ≤ p*y^s
   have hb: c x^k * y * M x *4*ψ ≤ 1:=le_trans (b:= c x^k*g x*M x*4*ψ) (by gcongr) ((le_abs_self _).trans hK)
   calc
     _ ≤ c x^k*w * ψ:= by gcongr; exact (sub_le_self _ zero_le_one).trans (Real.exp_monotone hu)
     _ = p*y^s * (c x^k * y*M x*4*ψ):=by unfold w; rw [pow_succ]; ring
     _ ≤ p*y^s:= mul_le_of_le_one_right (by positivity) hb
lemma funding (v d:ℝ→ℝ)(hv:Rate G L r v)(hr:r<0)(hd:Rate G L 0 d)(hσ:0≤ σ)(k s:ℕ): ∀ᶠ x in atTop, ∀ β,inBand (betaF G x L) β→∃ w t γ, Resonant (radiusB x) k |v x| (unitK x^4*gStep β^(s+1)) |d x| σ (unitK x^4*gStep β^s) w t γ:= Flues.buying (fun x=>unitK x^4) (Eventually.of_forall (fun x=> ⟨pow_pos (cheap x|>.1) _,pow_le_one₀ (cheap x|>.1.le) (cheap x|>.2)⟩)) v d hv hr hd hσ k s

variable {α:Type*}{ι:Type} {n : Side} {H : Yard ι α G n} {Z:Set ι} {P:BudgetPoint} {k m s:ℕ} {x β:ℝ}
lemma divided (h:H.Pays Z k P.B P.supportExponent (unitK x^4 * gStep β^s)) :
       ∃ f:ℕ→ℝ,(∀ i,0 ≤ f i) ∧ (∀ y:Site n,SumBudget (fun i=> if y∈H.plane i then P.mass (H.plane i) (f i) else 0) (gStep β^s)) ∧
            ∀ i, Mosaic.Verse.load Z (H.score i)≤ k → ∀ a V, ‖H.glow a i V‖/Real.sqrt (unitK x) ≤ f i:=by
   obtain ⟨q,hq,hh,hW⟩:=h.wages; let a:=Real.sqrt (unitK x)
   have hp:0<a:= Real.sqrt_pos.mpr (cheap x|>.1)
   have he : 0 ≤ gStep β:= inv_nonneg.mpr (Real.sqrt_nonneg _)
   have ht : 0 ≤ a⁻¹:=by positivity
   have hv := Quotes.hit_scale ht hh
   have hc:a⁻¹*(unitK x^4 * gStep β ^s)≤ gStep β^s:=by
      rw [← mul_assoc]; apply mul_le_of_le_one_left (pow_nonneg he _); rw [inv_mul_eq_div,div_le_one hp]; have hg : unitK x^4 ≤ unitK x:= (pow_le_pow_of_le_one (cheap x|>.1.le) (cheap x|>.2) (show 1≤(4:ℕ) by decide)).trans_eq (pow_one _); refine hg.trans ?_
      have hz:a≤1 := by unfold a; apply Real.sqrt_le_one.mpr; exact (cheap x).2
      rw [← Real.sq_sqrt (cheap x|>.1.le)]; change a^2 ≤ a; rw [pow_two]; exact mul_le_of_le_one_left hp.le hz
   refine ⟨fun i=>a⁻¹*q i,fun i=>mul_nonneg ht (hq _),fun i=>?_ ,fun i hi b V=>?_⟩
   · convert budget_loosen (hv i) hc using 1; ext x; unfold BudgetPoint.mass; split; ring; rfl
   dsimp only; rw [inv_mul_eq_div]; exact div_le_div_of_nonneg_right (hW i hi b V) hp.le
lemma at_scale (C:Levels G) (m:ℕ) : Real.sqrt (unitK (C.clock.hatBeta m))= Real.sqrt (C.clock.forcedAllowance m):=rfl
end YM.RemainderComparison.Flues
