import YM.RemainderComparison.Lacuna.Tall
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Song.Score
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Lacuna
open Function Filter Finset Lattice RG Wilson MeasureTheory ProbabilityTheory Ovens
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Work.E03 Work.F03
open PhysicalNext PhysicalNext.Repeat Song Slide Trio
open AnalyticBridge VerifiedReset Collection Quotes YM.Extra.Iteration
open Mosaic Mosaic.Verse WickReps Flues Lobby
open scoped Topology ContDiff BigOperators Classical Matrix.Norms.Frobenius
 variable {G:Gauge}{c:Side}{ι β I : Type}{α:Type*}[DecidableEq β]
open Marker Serif Manor Footprint
variable (T:Manor G c ι α I)(P:BudgetPoint) (u:Set ι)
local notation "Vʼ"=> night T u
-- all VAC Σ orientation. ignore VARYING Φ approved.Low.Core.Vol masks
-- output archive pre.E.Seeds
abbrev Total : Set (↑(night T u)) := {i| T.total i.val}
abbrev Region := (↑(night T u))
local notation "Tv"=> Lacuna.Total T u
local notation "Ω"=> Tvᶜ

structure Vowel (G:Gauge)(c:Side)(I:Type) where
    sign : I→ RegularAddress c
    stanza : I → Config G c→ℝ
namespace Vowel
variable (T:Vowel G c I)(P:BudgetPoint)
def ray (i:I):= masked P.threshold (T.sign i).support (T.stanza i)
def overlay : Config G c→ℝ:=fun U=>∑' i, T.ray P i U
-- before projection.W Quote. Pixel widths flexible.
structure Pricings (σ d:ℝ): Prop where
    fares :∃ u:I→ℝ,∀ i,0 ≤ u i -- redundant positivity.Smaller might drop (fill)
    marks :∃ u:I→ℝ,(∀ i,P.Regular (T.sign i).support (T.stanza i)∧ P.supBounds (T.sign i).site (T.sign i).support (T.stanza i) (u i)) ∧ Footprint.Anchored (fun i=>(T.sign i).site) u (fun i=>coverNumber P.B (T.sign i).support) σ d

structure Moves : Prop where
    continual (s:Signed)(b:Site c):∃ p:Equiv.Perm I,∀ i,T.sign (p i)=Song.line (T.sign i) (s,b)∧ T.stanza (p i)=T.stanza i ∘ pull s b
end Vowel
-- no negative yet.

def interior (b:α): Vowel G c (↑(Ω)) := ⟨fun i=> T.rooms i.val.val,fun i=> T.solvent b i.val.val⟩
def exterior (b:α): Vowel G c (Seat c× ↑((Lacuna.Total T u)ᶜ)):=
    ⟨Song.revolve (interior T u b).sign,Song.choir (interior T u b).stanza⟩
local notation "V₁" => Lacuna.interior T u
local notation "V₂" => Lacuna.exterior T u
lemma enroll (b:α): Vowel.Moves (V₂ b):=by
  refine ⟨fun s t=>⟨Song.whirl s t,fun i=>?_⟩⟩
  obtain ⟨h,hp,hh⟩:= Song.spirit (V₁ b|>.sign) (V₁ b|>.stanza) s t i
  have he: ∀ (P Q:RegularAddress c),P.site=Q.site→P.support=Q.support→P=Q:=by rintro ⟨_,_,_⟩ ⟨_,_,_⟩ a b; congr
  exact ⟨he _ _ h hp,hh⟩
local notation "L₁" => Seat c
lemma possession (b:α)(i: ↑(Ω))(U:Config G c): T.wet P b i.val.val U=Vowel.ray (V₁ b) P i U:= if_neg i.prop
variable {σ ψ:ℝ}{root:ι→Support c}
lemma earnings (b:α)(hp:T.Templary Vʼ root P σ ψ): Vowel.Pricings (V₂ b) P σ (turnFee P*ψ):=by
    obtain ⟨f,h,hG,he⟩:= hp.grants
    let X:= V₁ b; have hf (i: ↑(Ω)):= hG i.val.val i.val.prop
    let g (i:L₁× ↑(Ω)):= Rim c * (turnFee P * f i.2.val.val); have hg i:0 ≤ g i:= mul_nonneg (rim_nn _) (mul_nonneg (turnFee_pos _).le (h _))
    have ht : 0≤ψ:= Cost.nonneg (he (0:Site c))
    have ht': Rim c * (turnFee P * ψ)≥0:= mul_nonneg (rim_nn _) (mul_nonneg (turnFee_pos _).le ht)
    refine ⟨⟨g,hg⟩,⟨g,fun i=>?_,fun i=>?_⟩⟩
    · obtain ⟨y,i⟩:= i
      have hx:= (hf i).1.angle b; have hv:= CouplingShape.sup_scale (Rim c) (Song.transSup y hx ((hf i).2 b)); rw [abs_of_nonneg (Song.rim_nn _)] at hv; exact ⟨CouplingShape.reg_scale _ (Seat.regular y hx),hv⟩
    rw [show turnFee P*ψ=(Fintype.card L₁ :ℝ)*(Rim c*(turnFee P*ψ)) from (by rw [← mul_assoc,balance,one_mul])]
    apply Cost.product (Cost.finite (Rim c*(turnFee P*ψ)) ht')
    intro x; let y:=StepData.sendSites x.1 x.2; have hv (k:↑(Ω)) : coverNumber P.B ((V₂ b).sign (x,k)).support = coverNumber P.B (T.halls k.val.val):= Seat.visit_count ..
    have hh (k:↑(Ω)) : ((V₂ b).sign (x,k)).site=i ↔ T.port k.val.val=y.symm i := y.apply_eq_iff_eq_symm_apply
    let w (i:↑(Ω)):=i.val.val; have hx:= budget_pull w (Subtype.val_injective.comp Subtype.val_injective) (he (y.symm i)); have hj:= Cost.scale (Cost.scale hx (turnFee P) (turnFee_pos P).le) (Rim c) (rim_nn _)
    convert hj using 2 with j; unfold w; simp_rw [hv,hh]; unfold g; -- simplify rotations
    dsimp only [Function.comp_apply]
    split <;> ring
-- pay scalar separately as density offset exactly

def scalar (b:α):= ∑' i:Tv,T.wet P b i.val.val 1
lemma landed (a:α) (U:Config G c) (hp:T.Templary (night T u) root P σ ψ) (hσ:0≤ σ): (Vowel.overlay (V₁ a) P U) + Lacuna.scalar T P u a=aurora u T P a U:=by
    let f i:= T.wet P a (i:Vʼ).val U; have h:= peak T P hσ hp a U; have hl : Summable f:=h
    change _=∑' i,f i
    rw [← (hl.subtype (Tv)|>.tsum_add_tsum_compl (s:=Tv) (hl.subtype _))]
    obtain ⟨k,he,hG,hQ⟩:= hp.grants; unfold Lacuna.scalar Vowel.overlay
    have he (i:Tv): T.wet P a i.val.val 1=T.wet P a i.val.val U:=by unfold Manor.wet; rw [if_pos (show T.total _ from i.prop), if_pos (show T.total _ from i.prop)]; exact (hG _ i.val.prop|>.1|>.stall a i.prop U).symm
    rw [add_comm]; simp_rw [he]; apply congr_arg; refine tsum_congr fun i=>?_ ; rw [← possession]
structure Angular (P:BudgetPoint) (d ψ:ℝ) : Prop where
    summable a U : Summable fun i: ↑(Lacuna.Total T u)=> T.wet P a i.val.val U
    price a : ‖scalar T P u a‖ ≤ Fintype.card (Site c)*ψ
    stars a : Vowel.Pricings (exterior T u a) P d (turnFee P * ψ)

def revolves (f:Seat c→ℝ): ℝ:= (Rim c)*∑ x, f x
lemma ray_keeps (hp:T.Templary (night T u) root P σ ψ)(hσ:0≤ σ) (b:α)(U:Config G c) : Vowel.overlay (V₂ b) P U+scalar T P u b= revolves (fun x:Seat c=> aurora u T P b (x.view U)):=by
    let f:= (V₂ b).ray P; let X:= (V₁ b).ray P; let s (x:Seat c):= aurora u T P b (x.view U)
    have he (x: Seat c) : Summable fun i:↑(Ω)=> T.wet P b i.val.val (x.view U):= (peak T P hσ hp ..).subtype _
    have hx x: HasSum (fun k:↑(Ω)=> f ((x,k):L₁ × ↑(Ω)) U) ((Rim c)*(s x- scalar T P u b)):=by
       have hh : (∑' i:↑(Ω),T.wet P b i.val.val (x.view U))=s x-scalar T P u b:=by
           simp_rw [possession T P u b]; exact eq_sub_of_add_eq (landed T P u b (x.view U) hp hσ)
       rw [← hh]; exact ((he x).hasSum.mul_left (Rim c)).congr_fun fun i=> by rw [possession T P u b]; exact Song.tune ..
    have ht:= ConnectedActivityE6.Raw.finite_start (fun i=>f i U) _ hx
    rw [Vowel.overlay,show (∑' i,(V₂ b).ray P i U)= _ from ht.tsum_eq,revolves]
    unfold s; rw [← Finset.mul_sum, Finset.sum_sub_distrib,mul_sub,sum_const,card_univ,nsmul_eq_mul,← mul_assoc,mul_comm (Rim c) (Fintype.card L₁), Song.balance,one_mul]; ring
lemma angular (hp:T.Templary Vʼ root P σ ψ) (hs:0 ≤ σ): Angular T u P σ ψ :=by
    refine ⟨fun a U=> (peak T P hs hp a U).subtype _,fun a=>?_,fun a=> earnings T P u a hp⟩
    obtain ⟨f,h,hV,hF⟩:=hp.grants
    have he:SumBudget f (Fintype.card (Site c)*ψ):=by
       apply budget_of_sum h
       intro p
       have hh x : ∑ i ∈ p,(if T.port i=x then f i else 0) ≤ ψ:=le_trans (sum_le_sum fun i _=> ?_) (budget_sum (hF x) p)
       swap; · split_ifs; exact le_mul_of_one_le_right (h i) (Real.one_le_exp (mul_nonneg hs (by positivity))); exact le_rfl
       have hx : ∑ x:Site c,(∑ i ∈ p,if T.port i=x then f i else 0)= ∑ i∈p,f i:=by rw [sum_comm]; simp
       rw [← hx]; exact le_trans (sum_le_sum (fun i _=> hh i)) (by simp)
    have hg:=budget_pull (fun x:Tv=>x.val.val) (Subtype.val_injective.comp Subtype.val_injective) he
    have hv (i : Tv): ‖T.wet P a i.val.val 1‖ ≤ f i.val.val:= Manor.wet_le a 1 (hV i.val.val i.val.prop|>.1) ((hV i.val.val i.val.prop).2 a) -- check
    have hl:= budget_mono hg (fun i => norm_nonneg _) hv
    exact (norm_tsum_le_tsum_norm hl.2.1).trans hl.2.2
lemma still (x:Seat c→ℝ) {u:ℝ}(h:∀ i,x i=u): Lacuna.revolves x=u:=by unfold Lacuna.revolves; simp_rw [h]; rw [sum_const,card_univ,nsmul_eq_mul,← mul_assoc,mul_comm (Rim c),balance,one_mul]
lemma refrains (x y:Seat c→ℝ) : Lacuna.revolves (x+y)=Lacuna.revolves x+ Lacuna.revolves y:=by unfold Lacuna.revolves; simp only [Pi.add_apply,sum_add_distrib,mul_add]
end YM.RemainderComparison.Lacuna
