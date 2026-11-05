import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Cub.Arcs
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Daisy.Corral
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
section layer
include a
omit [DecidableEq ι] in
lemma tide (h:Walled S X Y x r)(hw:o∈X)(z:Prices G ι)(hv: 1 ≤ n): B.threshold*pitch n _ D.Z (Heir.scope B X r x) P.power z ≤ scratch (n:=n) G D P B Fq X r x * powers z^2:=by
   let K:= cup (n:=n) D P B X r x; have h₁ :1≤K:= canopy_one D.chimes _ _ _; have hg:= grows z
   let s:= Heir.scope B X r x; have hp : Carillon.pitch n (ι×G.ColorIndex) D.Z s P.power z≤ ((heads G B Fq X r x:ℕ):ℝ)^2*(K+1)*K*(powers z)^2:=by
     unfold Carillon.pitch; change _*(K+‖z‖^2)*_≤_
     have hi : ‖z‖^2≤powers z^2:= pow_le_pow_left₀ (norm_nonneg _) ((tape_control z).1.trans (tape_control z).2) _
     calc
       _ ≤ ((heads G B Fq X r x:ℕ):ℝ)^2*((K+1)*powers z^2)*K:=by
         gcongr ?_^2 * ?_ * _
         · exact Nat.cast_le.mpr (a.viewed h B hw G)
         rw [add_mul,one_mul]; exact add_le_add (le_mul_of_one_le_right (by positivity) (one_le_pow₀ hg)) hi
       _=_:=by ring
   apply (mul_le_mul_of_nonneg_left hp B.threshold_pos.le).trans; unfold scratch; let t:=(heads G B Fq X r x:ℝ)^2; let e:=t*(K+1)*K*powers z^2
   change _ ≤ _*_ * t * (K+1) * K* powers z^2
   have ht:1≤(n:ℝ):=Nat.one_le_cast.mpr hv; have hz:=B.threshold_pos
   calc
     _ ≤ n*(2*B.threshold)*e:= by apply mul_le_mul_of_nonneg_right _ (by have ht:0≤ t:=sq_nonneg _; positivity); nlinarith
     _ = _:= by unfold e; ring
end layer
-- communal small post pigment. works with Ξ.Gpost. At trueX. χ margin.

def opal (C:Libretto G n)(D:Record)(P B:BudgetPoint)(Lx:Side)(X:Support f)(r:ℕ)(x u:ℝ):= Lute.rust C D P B Lx X r x u + (16 / D.ε)*ζ B u
lemma opal_nn (C:Libretto G n)(D:Record)(P B:BudgetPoint)(Lx: Side)(X:Support f)(r:ℕ)(x u:ℝ)(hu:0 ≤ u):0≤opal C D P B Lx X r x u:=add_nonneg (rust_nn hu) (mul_nonneg (by have h:=D.guards; positivity) (add_nonneg B.threshold_pos.le (by have h:=B.threshold_pos; positivity)))

include hu
omit [DecidableEq ι] in
lemma sunny (z:Prices G ι):
     let J:=opal C D P B Fq X r x u; let t:=J*powers z^2
     ‖θ! z-1‖ ≤ t ∧ p! (u*‖tape z‖) ≤ t:=by
    intro J t; let p:=powers z; let r0:= rust C D P B Fq X r x u
    have hP:0 ≤ J:=opal_nn C D P B Fq X r x u hu.le -- edit
    let e:= D.ε
    have hv:0<e:=D.guards
    let a:= B.threshold; have hB:0<a:=B.threshold_pos; have ht:1≤p:= grows z
    have hJ:r0 ≤ J:=le_add_of_nonneg_right (mul_nonneg (by change 0≤16/e; positivity) (show 0≤ζ B u from add_nonneg hB.le (by have :=B.threshold_pos; positivity)))
    have hy:‖tape z‖≤ p^2:= (tape_control z).2.trans (le_self_pow₀ ht two_ne_zero)
    constructor
    · by_cases he :∀ i,u*‖tape z i‖ ≤ e*a/8
      · rw [guard_open Γ hu (mul_pos hv hB) he,sub_self,norm_zero]; exact mul_nonneg hP (sq_nonneg p)
      push Not at he
      obtain ⟨i,hi⟩:=he
      have hh : u/a*p^2≥ e/8:= by apply le_of_mul_le_mul_right _ hB; rw [mul_right_comm _ _ a,div_mul_cancel₀ _ hB.ne']; exact ((show e/8*a=e*a/8 by ring).le.trans hi.le).trans (mul_le_mul_of_nonneg_left ((norm_le_pi_norm _ _).trans hy) hu.le)
      have hm: J * p^2 ≥ 2:=by
         have hg:=Lute.rust_nn (C:=C) (D:=D) (X:=X) (L:=Fq) (P:=P) (B:=B) (x:=x) (r:=r) hu.le
         calc
           (2:ℝ) = (16/e)*(e/8):=by field_simp; ring
           _ ≤ (16/e)*(u/a*p^2):=mul_le_mul_of_nonneg_left hh (by positivity)
           _ = ((16/e)*(u/a))*p^2:=by ring
           _ ≤ _:=mul_le_mul_of_nonneg_right ((mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hB.le) (show 0≤16/e by positivity)).trans (le_add_of_nonneg_left hg)) (sq_nonneg _)
      refine (norm_sub_le ..).trans ?_; rw [norm_one]; have hp:= (guard_silent Γ hu (mul_pos hv hB) (I:=ι) (n:=0)).little z; change _ ≤ J*p^2; exact (le_trans ((add_le_add_left hp 1).trans (le_of_eq (by ring))) hm) -- edit
    have hL : 1 ≤ ((S.patch.L.val:ℝ)) := Nat.one_le_cast.mpr (S.patch.L.property)
    let K:=loom P (reach x) C.C
    have hh: 0≤clinicFee n D.Q:=(mul_nonneg zero_le_two (zero_le_one.trans D.majorant)).trans (clinicFee_le _ (zero_le_one.trans D.majorant))
    have hr₀ : p! (u*‖tape z‖) ≤ p! u * p^2:=by
      unfold paint; rw [div_mul_eq_mul_div]; apply div_le_div_of_nonneg_right _ B.threshold_pos.le; rw [add_mul]; exact add_le_add (le_mul_of_one_le_right (mul_nonneg hh (sq_nonneg _)) (one_le_pow₀ ht)) ((mul_le_mul_of_nonneg_left hy hu.le).trans_eq (by ring))
    have hp: p! u ≤ tranche Fq n D.Q K u B.threshold := le_mul_of_one_le_right (painting_pos C D P B x u hu.le) (one_le_pow₀ hL)
    apply hr₀.trans
    have hb: tranche Fq n D.Q K u B.threshold ≤ r0:= (le_add_of_nonneg_left (segment_nn n X P B D.majorant C.matins)).trans (le_add_of_nonneg_right (scratch_nn n))
    exact mul_le_mul_of_nonneg_right ((hp.trans hb).trans hJ) (sq_nonneg p)
end YM.PhysicalNext.Repeat.Cub
