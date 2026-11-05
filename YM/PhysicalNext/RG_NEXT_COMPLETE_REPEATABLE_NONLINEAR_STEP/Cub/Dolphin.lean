import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Amber
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Quartz
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Peak.Puff
/-!
 # Price spiral: Γ hard.V9.Price z.K not used for derivative.Z.Stock cost when not plateau, absorb tiny. ALL envelopes from inherited naked normalized no holes.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Cub
open Function Filter Set Lattice Wilson Pressure Precision RG Tree Next Next.SectorChange Next.Fluctuations WardBin.Lies
    Matrix Multi Multi.Vacuum.Jets Multi.Puff ProofPorts.CommonComplexProduction ProofPorts.CommonComplexProduction.Score
    AnalyticBridge.LocalGaussianLaws Metric
open Planned.AtomRegular JointLoad JointLoad.Heir Lute Heir.Carillon Push Push.SectorMeasure Next.Foundations
open AnalyticBridge.LocalGaussian.Moments
open MeasureTheory
open scoped Topology ContDiff Matrix.Norms.Frobenius BigOperators Classical
variable {G : Gauge} {c f : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {A : Stores S} {X : Support f} {Y : Support c}
    {P B : BudgetPoint} {ι : Type} [Fintype ι] [DecidableEq ι] {x u t τ : ℝ} {n r m : ℕ} {o : Site f}
    {q : Chi} {d : ℝ} {k : S.Choices} {f' : Config G f → ℝ} {Pt : Teller G} {C : Libretto G n} {D : Record}
variable (a:Museum F x A X Y ι)(U:Config G f)
    (he: Plays C D P B Pt T x)(hf:B.Regular X f')(hτ:B.supBounds o X f' τ)(ho:o∈X)(hs: Short S B X)(hm: m+1 ≤ n)
    (hY: Walled S X Y x r)
variable (q d k) (Γ:Chi)(hu:0<u)
local notation "z0"=> (1:Config G c)
local notation "f₀"=> deem o x T f'
local notation "f!"=> Complex.ofRealCLM ∘ f₀ -- set option
local notation "θ!"=> guard Γ G ι u (D.ε*B.threshold)
local notation "p!"=> paint C D P B x
local notation "Fq"=> S.patch.L
set_option quotPrecheck false
local notation "J"=> opal C D P B S.patch.L X r x u
local notation "w"=> B.threshold
local notation "Y0"=> Heir.scope B X r x
local notation "b" => P.power
local notation "V0"=> P.dirBound (S.ratio.parent o)
variable (hw:opal C D P B S.patch.L X r x u ≤ 1)
include he hτ hf hm ho hu hY hs hw
set_option maxHeartbeats 450000 in
private lemma funded (z:Prices G ι) : let H:= powers z^2; let g:=J
    Band m (P.dirBound (S.ratio.parent o)) z0 (((n:ℝ)*4+1)*H) ((devBill C τ 1+2*reachBill C τ)*g*H^(n+1)) (a.concert T u q d k f' θ! U z0 z-f!):=by
   intro H J0; have hT:=hu.le
   obtain ⟨hf₀,hy⟩:=sunny (S:=S) (C:=C) (X:=X) (P:=P) (B:=B) (x:=x) (r:=r) Γ hu z (D:=D)
   let v:= w*pitch n _ D.Z Y0 b z
   have hg:1≤H:=one_le_pow₀ (grows z)
   have hd:0 ≤ J0:=opal_nn C D P B S.patch.L X r x u hu.le
   have h : v ≤ J0*H:=by
      have hk : scratch (n:=n) G D P B S.patch.L X r x ≤ J0:=by
          have hz: rust C D P B S.patch.L X r x u ≤ J0:= le_add_of_nonneg_right (mul_nonneg (by have h:=D.guards; positivity) (show 0≤ ζ B u from add_nonneg B.threshold_pos.le (by have h:=B.threshold_pos; positivity)))
          apply le_trans _ hz; unfold rust; exact le_add_of_nonneg_left (add_nonneg (segment_nn n X P B D.majorant C.matins) (tranche_nn _ _ (zero_le_one.trans D.majorant) hu.le B.threshold_pos.le))
      exact (Cub.tide a hY ho z (by omega)).trans (mul_le_mul_of_nonneg_right hk (by positivity))
   apply band_rise (hues q d k a U he hf hτ ho hs hm hY θ! hT (guard_silent Γ hu (mul_pos D.guards B.threshold_pos)) z) -- arg maybe
   · let p:= p! (u*‖tape z‖); let C':= C.rights.fee; have ht:= patterns_nonneg n; have hH:= C.matins; have hC:= C.rights.large; have hZ:=hτ.1; let r0:=reachBill C τ; have hr:r0≥0:=by unfold r0 reachBill wealth; positivity
     have hv : devBill C τ p ≤ devBill C τ 1*J0*H^(n+1):=by
       have hz:0≤ wealth C:=by unfold wealth; positivity
       have hr: wealth C+p≤ (wealth C+1)*H:=by rw [add_mul,one_mul]; exact add_le_add (le_mul_of_one_le_right hz hg) (hy.trans (mul_le_of_le_one_left (by linarith) hw))
       have hp:p≥0:=painting_pos C D P B x (u *_) (mul_nonneg hT (norm_nonneg _))
       unfold devBill; calc
         _ ≤ patterns n * ((1+(2:ℝ)^n)*((J0*H)*((wealth C+1)*H)^n*C.rights.fee*τ)):=by gcongr
         _ = _:=by rw [mul_pow]; ring
     let y':=r0*J0*H^(n+1); have hh : J0*H*r0 ≤ y':= (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (le_self_pow₀ hg (Nat.succ_ne_zero n)) hd) hr).trans_eq (by change J0*H^(n+1)*r0=r0*J0*H^(n+1); ring)
     exact le_trans (add_le_add (add_le_add hv ((mul_le_mul_of_nonneg_right h hr).trans hh)) ((mul_le_mul_of_nonneg_right hf₀ hr).trans hh)) (le_of_eq (by unfold y' r0; ring))
   have ht:v≤ H:=h.trans (mul_le_of_le_one_left (by positivity : 0≤ H) hw); change _ + 1 ≤ _; unfold Carillon.speed; change n * (1+v) * 2 + 1 ≤ _; nlinarith only [mul_le_mul_of_nonneg_left ht (Nat.cast_nonneg (α:=ℝ) n),mul_le_mul_of_nonneg_left hg (Nat.cast_nonneg (α:=ℝ) n),hg]

-- dimension meters any n. actual authority Relief prices polynomial. literal Stcrum.
def clocks (C : Libretto G n)(τ:ℝ):=(devBill C τ 1+2*reachBill C τ)*((n:ℝ)*4+1)^n
omit he hτ hf hm ho hu hY hs hw in
lemma clocks_pos (C:Libretto G n){τ:ℝ}(h:0≤ τ): clocks C τ≥0 := by have h:= C.matins; have hi:=C.rights.large; have ht := patterns_nonneg n; unfold clocks devBill reachBill wealth; positivity -- include.T syntax omit
local notation "N'"=> 2*((n+1)+(n+1))
-- True derivative through THIS record normalized. Any l
lemma gasket (l:List (Directions G c))(hl:l.length≤ m)(hb:∀ i∈l,P.dirBound (S.ratio.parent o) i):
    let h:= a.hymn T u q d k f' (guard Γ G ι u (D.ε*B.threshold)) U
    ‖leftDerivs h l 1-leftDerivs (deem o x T f') l 1‖ ≤ clocks C τ * J * AnalyticBridge.LocalGaussian.Moments.meter (heads G B S.patch.L X r x) 0 D.K (2*((n+1)+(n+1))) := by
   intro h; obtain ⟨hC,hI,H⟩:=Peak.opaqueE q d k a U he hf ho hY hu.le (guard_silent Γ hu (mul_pos D.guards B.threshold_pos)) (one_healthy Y _ P.threshold_pos.le) l (hl.trans (by omega)); let μ:= Gaussian.cloud (a.twilight k T z0)
   let f₁:= (f!); let z':=leftDerivs f₁ l z0
   have hξ:= deem_focus (o:=o) he hf; have hh : z'=Complex.ofReal (leftDerivs (deem o x T f') l z0):=Push.Local.left_linear Complex.ofRealCLM l hξ.germ (hl.trans (by omega));
   let V(z: Prices G ι):= a.concert T u q d k f' θ! U z0 z; let M(z):= leftDerivs (V z) l z0
   have ht:= he.cantos (k:=k) a (one_healthy _ _ P.threshold_pos.le) hY ho
   let N:= 2*((n+1)+(n+1)); let U₁:= (opal C D P B S.patch.L X r x u); have hv:= clocks_pos C hτ.1; have hP:U₁≥0:=opal_nn C D P B S.patch.L X r x _ hu.le
   have ha (z) : ‖M z-z'‖ ≤ clocks C τ*U₁*powers z^N:= by
      have h:=funded q d k a U he hf hτ ho hs hm hY Γ hu hw z
      have he': Multi.Puff.Crest m f₁ z0:= crest_cast.mpr (into m _ (hξ.germ.of_le (Nat.cast_le.mpr (Nat.le_of_lt hm))))
      have hs : Multi.Puff.Crest m (V z) z0:= by
          have ht':V z=(V z-f₁)+f₁ := (sub_add_cancel ..).symm
          exact ht'.symm ▸ into m ((V z - f₁)+ f₁) (h.readable.germ.add he'.germ)
      rw [show M z-z'= _ from (redacted hs he' hl).symm]; apply (h.caps l hl hb).trans
      let wT:=powers z^2; have hx:1≤wT:=one_le_pow₀ (grows z)
      let v := (n:ℝ)*4+1; have hv:1≤v:=by unfold v; linarith [Nat.cast_nonneg (α:=ℝ) n]
      let T:= (devBill C τ 1+2*reachBill C τ)*U₁*wT^(n+1); have ht:0≤T:=h.nonneg
      apply (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (one_le_mul_of_one_le_of_one_le hv hx) (hl.trans (Nat.le_of_lt hm))) ht).trans
      unfold clocks; let H':=devBill C τ 1+2*reachBill C τ; calc
        _ = H'*v^n*U₁*wT^(n+1+n):=by change H'*U₁*wT^(n+1)*(v*wT)^n = _; rw [mul_pow,pow_add]; ring
        _ ≤ _:=by unfold N; rw [pow_mul]; exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hx (by omega)) (mul_nonneg (clocks_pos C hτ.1) hP)
   have htK:= D.peak; obtain ⟨hq,hY'⟩:= purchased ∅ (zero_lt_one.trans_le htK) ht.pos ht.peak N
   change MeasureTheory.Integrable (fun z=> slopeEnvelope ∅ D.K N z) _ at hq
   simp only [slopeEnvelope,load,Finset.sum_empty,mul_zero,Real.exp_zero,mul_one,Finset.card_empty] at hq hY'
   have hb : (∫ z,powers z^N ∂μ) ≤ AnalyticBridge.LocalGaussian.Moments.meter (heads G B S.patch.L X r x) 0 D.K N:= by
      apply hY'.trans; unfold AnalyticBridge.LocalGaussian.Moments.meter; have hx := a.viewed hY B ho G; have hK:=inflate_ge N (by positivity : 0 ≤D.K⁻¹/8)
      gcongr <;> exact hx
   rw [← Complex.norm_real, Complex.ofReal_sub,← hh]; change ‖((leftDerivs h l z0:ℝ):ℂ)-z'‖ ≤ _; rw [show ((leftDerivs h l z0:ℝ):ℂ)=∫ z,M z ∂μ from H,show (∫ z,M z ∂μ) - z'= ∫ z,M z-z' ∂μ from by rw [integral_sub hI (integrable_const _),integral_const,MeasureTheory.probReal_univ,one_smul]]
   refine (norm_integral_le_integral_norm ..).trans ((integral_mono ((hI.sub (integrable_const z')).norm) (hq.const_mul (clocks C τ * U₁)) ha).trans ?_)
   rw [integral_const_mul]; exact mul_le_mul_of_nonneg_left hb (mul_nonneg hv hP)
end YM.PhysicalNext.Repeat.Cub
