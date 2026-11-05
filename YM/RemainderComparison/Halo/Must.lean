import YM.RemainderComparison.Halo.Strike

/-! # Finite epoch precision compiler; no unsupported `Rate 0` purchased from Monitor. -/
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Halo
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Graft Cascade Lyric Daisy
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {L : Side} {P:Teller G}
lemma lumens (Q:ConnectedActivityE6.Target G P) {p Δ:ℝ→ℝ}{j k:ℕ} (a:ℝ) (hh:Reserve G L p)(ht:Reserve G L Δ):
    Reserve G L (fun s=>rebate Q (p s) (Δ s) j k) ∧ Reserve G L (fun s=>collars G a s j k):=by
   -- generic parameter arrests at scope
   let e:= Reserve.const (G:=G) (L:=L)
   have h : Reserve G L shiftG:= (e _).mul (((e _).mul Reserve.field).add (e _))
   exact ⟨((e _).add ((e _).mul hh)).mul ((e _).mul ((ht.mul (e _)).mul (e _))), (h.pow _).mul (e _)⟩
lemma hikes (Q:ConnectedActivityE6.Target G P) {p : ℝ→ℕ}{Δ:ℝ→ℝ} (h:Reserve G L (fun x=>(p x:ℝ)))(hv: Reserve G L Δ) : Reserve G L (fun x=> hike Q x (p x) (Δ x)):=by
   have ht (c:ℝ):=Reserve.const (G:=G) (L:=L) c
   unfold hike
   refine (h.mul ?_).mul ((ht _).mul hv)
   unfold Extra.Multi.siteFactor
   have hp:= Reserve.field (G:=G) (L:=L)
   exact (ht _).mul (((ht 2).mul (((ht 16).mul hp).add (ht 9))).pow _)
lemma shade_reb (Q:ConnectedActivityE6.Target G P) {p:ℝ→ℝ}{j k:ℕ} (hp:Reserve G L p)(a:ℝ):
    Reserve G L (fun x=> degreePrice (radiusB x) (rebate Q (p x) 1 j k) a):=by
   unfold degreePrice Trees.stretch; simp_rw [div_eq_mul_inv]
   refine (Reserve.const _).mul (((Reserve.ball _ Reserve.field).mul ((lumens Q a hp (Reserve.const (1:ℝ))).1)).mul (Reserve.const _))

variable (Q:ConnectedActivityE6.Target G P)
structure Writ (Q:ConnectedActivityE6.Target G P) (L:Side)(μ x C' A₁ C₁ τ γ S' Δ Y ε:ℝ) (p j n:ℕ) : Prop where
    pace : 1≤ τ
    income : 1≤ S'
    awake : 0<γ
    beat : first (S'*A₁) (Q.costs L μ 1 x C').rootHit τ⁻¹ C₁ (|Halo.cost L Q x|) (hike Q x p (τ⁻¹*Y)) ≤ γ
    fits : τ* (incomingE G L x)*S' ≤ 1
    warmth : degreePrice (radiusB x) γ Q.δ ≤ 1/2
    height : degreePrice (radiusB x) (rebate Q Δ γ j n) ε ≤ 1/2
    cap : incomingE G L x≤ 1
    shape : radiusB (betaF G x L) ≤ 2*radiusB x
section
lemma stimulus (a:ℝ) : Reserve G L (fun x=> degreePrice (radiusB x) 1 a):=by
    unfold degreePrice Trees.stretch; simp_rw [div_eq_mul_inv]
    exact (Reserve.const _).mul ((((Reserve.ball _ Reserve.field).mul (Reserve.const _)).mul (Reserve.const _)))
lemma gear_writ {κ : ℝ}{j n:ℕ}{L:Side}(D:ℝ) {Y : ℝ→ℝ} (hY:Reserve G L Y)(p:ℝ→ℝ)(hp:Reserve G L p){μ:ℝ}(hm:0<μ)(ε:ℝ)
    {A:ℝ→ℝ}(h:Rate G L 0 A)(J:ℝ→ℕ)(hJ:Reserve G L (fun s=>(J s:ℝ))) : ∃ v, 0<v∧ ∃ (τ γ S' :ℝ→ℝ), Reserve G L τ ∧ Reserve G L γ ∧ Gear G L (-v) (fun x=>(S' x)⁻¹) ∧ ∀ᶠ x in atTop,
        Writ Q L μ x D (A x) κ (τ x) (γ x) (S' x) (p x) (Y x) ε (J x) j n:=by
    -- earn split, choose first S' cost via Rate Q.rate; cap Q> -(1/2)
    let W x:= κ*|cost L Q x|; let X x:= hike Q x (J x) (Y x)
    let a x:= degreePrice (radiusB x) 1 Q.δ; let b x:= degreePrice (radiusB x) (rebate Q (p x) 1 j n) ε
    let d x:=1+|a x|+|b x|; let D' x:= (3:ℝ)*d x; let i x:=(D' x)⁻¹; let c x:=1+|W x|+|X x|; let τ x:= 2*D' x*c x
    let f:=(fun x=> (betaF G x L)); let r:= -Q.rate /2; let S' x:= (f x)^r
    have hr : 0<r :=by unfold r; linarith [Q.stop]
    have ht: Reserve G L X:= hikes Q hJ hY
    have hb:= shade_reb (j:=j) (k:=n) Q hp ε
    have hg : Reserve G L W := (Reserve.const _).mul (cost_p G P Q L).absolute
    have he s : 1≤d s:= (le_add_of_nonneg_right (abs_nonneg _)).trans (le_add_of_nonneg_right (abs_nonneg _))
    have he' s:1≤c s:= (le_add_of_nonneg_right (abs_nonneg _)).trans (le_add_of_nonneg_right (abs_nonneg _))
    have hp' s:1≤D' s:= by unfold D'; linarith [he s]
    have hD : Reserve G L D':= (Reserve.const _).mul (((Reserve.const _).add (stimulus Q.δ).absolute).add hb.absolute)
    have hτ:Reserve G L τ:=((Reserve.const _).mul hD).mul (((Reserve.const _).add hg.absolute).add ht.absolute)
    have hh:Reserve G L i:=(Reserve.const 1).compare (Eventually.of_forall fun x=>by have ht:=hp' x; unfold i; rw [abs_of_pos (by positivity : 0 < (D' x)⁻¹),abs_one]; exact inv_le_one_of_one_le₀ ht)
    have hc:= Rate.power (G:=G) (L:=L) (a:=r)
    have hA:=(((hc.mul h).mul (Q.rate_root (C:=D) (β:=1) L hm)).mul hD.rate)
    refine ⟨r,hr,τ,i,S',hτ,hh,Gear.power.congr ((Delay.shift_pos G L).mono fun x hx=> (Real.rpow_neg hx.le _).symm),?_⟩
    have hT: r+0+Q.rate+0 <0:=by unfold r; linarith [Q.stop]
    filter_upwards [(Work.E09.betaF_growth G L).eventually_ge_atTop 1,hA.below hT _ (by norm_num : (0:ℝ)<1/2),((hτ.rate.mul (incomingE_rate G L)).mul hc).below (by unfold r; linarith only [Q.start]) _ zero_lt_one,(incomingE_rate G L).below (by norm_num) _ zero_lt_one, Fees.horizons G L Q.halo Q.usable Q.bound (show 2*Q.ε<P.top.supportExponent from (by linarith [Q.grants.1,Q.usable]))] with x hx hk hm' hf hs
    have hS: 1 ≤ S' x:= Real.one_le_rpow hx hr.le
    have hy : 1≤τ x := one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le one_le_two (hp' x)) (he' x)
    have hd :0<D' x:= zero_lt_one.trans_le (hp' x); have hp':0< i x:=by unfold i; positivity
    let s := S' x * A x * (Q.costs L μ 1 x D).rootHit
    have hz:s≤ i x/2:=by
       have hz:s*D' x ≤ 1/2:= (le_abs_self _).trans hk; have h: i x/2=(1/2)/(D' x):=by unfold i; ring
       rw [h]; exact (le_div_iff₀ hd).mpr hz
    have hδ:τ x*incomingE G L x*S' x ≤ 1:= (le_abs_self _).trans hm'
    refine ⟨hy,hS,hp',?_,hδ,?_,?_,(le_abs_self _).trans hf,hs.2.1⟩
    · unfold first; rw [show hike Q x (J x) ((τ x)⁻¹*Y x)=(τ x)⁻¹*(X x) from ?_,add_assoc,  mul_assoc (τ x)⁻¹,← mul_add] -- might wrong assoc
      swap; · unfold X hike; ring
      have he : W x+X x≤ c x:=by unfold c; linarith [le_abs_self (W x), le_abs_self (X x)]
      apply le_trans (add_le_add hz (mul_le_mul_of_nonneg_left he (by positivity)))
      unfold i τ; apply le_of_eq; have h:0<c x:=zero_lt_one.trans_le (he' _); field_simp; ring
    · have hh: degreePrice (radiusB x) (i x) Q.δ=a x/(D' x):=by unfold a degreePrice Trees.stretch i; ring
      rw [hh]; apply (div_le_iff₀ hd).mpr; unfold D' d; have hz:= he x; unfold d at hz; linarith [abs_nonneg (b x), le_abs_self (a x)]
    have hh: degreePrice (radiusB x) (rebate Q (p x) (i x) j n) ε=b x/(D' x):=by unfold b degreePrice Trees.stretch rebate treeYield i; ring
    rw [hh]; apply (div_le_iff₀ hd).mpr; unfold D' d; have hz:= he x; unfold d at hz; linarith [abs_nonneg (a x), le_abs_self (b x)]
end
end YM.RemainderComparison.Halo
