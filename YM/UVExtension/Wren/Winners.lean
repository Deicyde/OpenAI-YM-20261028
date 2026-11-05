import YM.UVExtension.Wren.Area
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wren
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze March Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι} {P:BudgetPoint}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine PhysicalNext.Repeat PhysicalNext.Repeat.Match PhysicalNext.Repeat.Greenbelt Wick
open Polar Silica Shield Score Flux Matter Ursell Gas Trees Multiple Refrain

-- Captain leases come together with Score width for all L large and at any calendar.
open AnalyticBridge VerifiedReset Collection Quotes WilsonStartup Extra.Iteration Next.Scheduling
open Song Strata Gala Concert Geo
namespace Chains
-- High stanza: bounded analytic stages and explicit l¹ threshold gains. still purchase actual width.
structure Flo (v:Filter ι)(u:ℝ) (V:ι→ℕ→ Atom G k)(T:ℕ→ Atom G k):Prop where
     width :0<u
     legs i j : (V i j).leg=(T j).leg
     gauges i j : (V i j).Invariant
     usher : (∀ j y,Tendsto (fun n=>(V n j).coeff y) v (𝓝 ((T j).coeff y)))
     pen : Swift v fun i j=> (V i j).budget u
namespace Flo
variable {A:ι→ℕ→ Atom G k}{S:ℕ→Atom G k} (h: Flo v u A S)

def place (x:ℕ): RegularAddress c:= ⟨0,(S x).footprint 0,mem_image.mpr ⟨0,mem_insert_self ..,by simp⟩⟩
-- archive align
include h
lemma seats (x:ℕ) (i): (S x).footprint (0:Site c)=(A i x).footprint 0:=by unfold Atom.footprint Atom.stencil; rw [h.legs]
lemma costSines (P:BudgetPoint){β:ℝ} : Swift v (fun i n=> sine P (A i) β n):=by -- use Wages. growth moment. inequality exp purchase single.
   let v':= ((|VerifiedReset.factor*β|)*turnFee P)*(highFee G k P u)*P.threshold^k; have hv:0≤ v':=by unfold v'; have :=highFee_pos G P k h.width; have :=turnFee_pos P; have :=P.threshold_pos; positivity
   apply (h.pen.scales v' hv).le; filter_upwards with i n
   let x:=(A i n); have hA:= Wages.scan P x -- inspect
   have hB:=h.width; let a:ℝ:= Wages.grade k P.power P.order
   let b:=Wages.startup G k P.power P.order; let s:= sine P (A i) β n
   let d:=(1+(x.length:ℝ)); let t:=(x.length:ℝ); have hx:s = v' *(x.magnitude*d^(Wages.grade k P.power P.order)) / momentPrice (Wages.grade k P.power P.order) (u/2):=by
       have hv:= momentPrice_pos (Wages.grade k P.power P.order) (half_pos h.width)
       unfold s sine v' d highFee; rw [hA]; field_simp ; ring
   refine ⟨sine_pos ..,?_⟩; change s ≤ v'*x.budget u; rw [hx]; let m:=Wages.grade k P.power P.order; let z:=momentPrice m (u/2); have ht:0≤t:= by unfold t; positivity
   have he : d^m ≤ z*Real.exp (u*t):=(spendMoment m (half_pos h.width) ht).trans (mul_le_mul_of_nonneg_left (Real.exp_monotone (by nlinarith)) (momentPrice_pos m (half_pos hB)).le)
   apply (div_le_iff₀ (momentPrice_pos m (half_pos hB))).mpr; unfold Atom.budget
   have hV := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left he (show 0≤x.magnitude by unfold Atom.magnitude; positivity)) hv
   exact hV.trans_eq (by unfold m z t; ring)
-- easiest direct rotor sup without scaling. Extend left test continuity by using Difference Atom via polynomial linear. prove via synthetic.
private def cut (x:ι×ι)(j:ℕ): Atom G k:= {A x.1 j with coeff:= (A x.1 j).coeff-(A x.2 j).coeff}
private lemma incision (x:ι×ι)(j:ℕ)(V: Fin k→G.Color) : (cut (A:=A) x j).poly V=(A x.1 j).poly V-(A x.2 j).poly V:=by unfold cut Atom.poly; simp only [Pi.sub_apply, sub_mul,sum_sub_distrib]
lemma choral (P:BudgetPoint)(x:Stave (n:=c)) (β:ℝ): Tendsto (fun n=> sine P (cut (A:=A) n) β x.2) (v×ˢv) (𝓝 0):=by
    let j:=x.snd; let f n:=(cut (A:=A) n j).magnitude
    have ht (y:Fin k→G.ColorIndex): Tendsto (fun n:ι×ι=> |(cut (A:=A) n j).coeff y|) (v×ˢv) (𝓝 0) := by
        have hx:=h.usher j y; simpa only [sub_self,abs_zero] using! ((hx.comp tendsto_fst).sub (hx.comp tendsto_snd)).abs
    have he:Tendsto f (v×ˢv) (𝓝 0):= by simpa only [Finset.sum_const_zero] using! tendsto_finsetSum Finset.univ (fun i _=> ht i)
    let c' := |VerifiedReset.factor*β| * (turnFee P * (Wages.startup G k P.power P.order* P.threshold^k * (((S j).length+1:ℝ)^ Wages.grade k P.power P.order)))
    apply ((show c'*0=(0:ℝ) from mul_zero _) ▸ he.const_mul c').congr'; filter_upwards with n; unfold sine; rw [Wages.scan]; let t:=(S j).length; change c'*f n=_; rw [show (cut (A:=A) n x.2).length=t from ?_]
    · unfold c' t; change _*( _ *( _*_*_)) *f n = _*(_*(_*_*f n*_)); ring
    unfold cut Atom.length; dsimp only; rw [h.legs]; rfl
lemma landsH (i) (x:Stave (n:=c)): pitch S x=pitch (A i) x:=by
    let e:Seat c:= x.1; have ht : (S x.2).footprint (0:Site c)=(A i x.2).footprint 0:=h.seats x.2 i; unfold Song.pitch; congr 1
lemma windward (P:BudgetPoint)(b:ℝ): Notes v P (pitch S (n:=c)) (fun n=>tuneAtom (A n) b) :=by
    have he i (j:Stave (n:=c)) : P.Regular (pitch S j).support (tuneAtom (A i) b j)∧ P.supBounds (pitch S j).site (pitch S j).support (tuneAtom (A i) b j) (sine P (A i) b j.2):=by rw [landsH h]; exact pitch_charge P (A i) j b (h.gauges _)
    have hK : Swift v (fun i (z:Seat c)=> (1:ℝ)):=Swift.sight (fun i=>⟨1,Eventually.of_forall fun _=> ⟨zero_le_one,le_rfl⟩⟩)
    apply Notes.rates.mpr
    refine ⟨fun i j=> (he i j).1,⟨_,hK.mixes (h.costSines P (β:=b)), Eventually.of_forall fun i j=>?_⟩,fun j ε hv=> ?_⟩
    · rw [one_mul]; exact (he _ _).2
    filter_upwards [(choral h P j b).eventually_le_const hv] with n hn
    let c:=cut (A:=A) n; have hu (i) x:=incision h n i x -- Include
    have hC (i): (c i).Invariant := fun t z=> by change (cut _ _).poly _=_; rw [hu, (h.gauges _ _ t z), (h.gauges _ _ t z),hu]
    have hx : tuneAtom (A n.1) b j-tuneAtom (A n.2) b j=tuneAtom c b j:=by
        let i:= j.2; let P:=j.1; let a:= VerifiedReset.factor*b; funext x; change a*(A n.1 i).unmasked (P.view x) 0-a*(A n.2 i).unmasked _ _= a*(cut (A:=A) n i).unmasked _ _
        rw [← mul_sub]; unfold Atom.unmasked; rw [hu]; change a*((A n.1 i).poly _- (A n.2 i).poly _)=a*((A n.1 i).poly (fun j=> ((A n.1 i).leg j).atSite (P.view x) 0)- (A n.2 i).poly (fun j=> ((A n.1 i).leg j).atSite (P.view x) 0))
        simp_rw [h.legs]; rfl
    rw [hx,h.landsH n.1]; exact VerifiedReset.sup_le (pitch_charge P c j b hC).2 hn -- signature
lemma winds (P:BudgetPoint) (d:ι→ℝ){t:ℝ}(he:Tendsto d v (𝓝 t)): Notes v P (pitch S (n:=c)) (fun n=> tuneAtom (A n) (d n)):=by
    have hh: (fun i j=> d i • tuneAtom (A i) 1 j)=(fun n=>tuneAtom (A n) (d n) (n:=c)):= by funext i j; unfold tuneAtom; rw [smul_smul,mul_one,mul_comm]
    rw [←hh]; exact (h.windward ..).swells d he
end Flo
end Chains
end YM.UVExtension.Wren
