import YM.RG08.Taste.Manor
/-!
# Canonical report retrieval. Master recording at $g_k$, all other heights re-expressed. 
Projection report at bottom sees exactly returned material. For V no marked vacuum removed. Supports across physical changes require RG04.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Taste
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Place Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Drift Pivot
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {I J W:Type} {u:I→Windows}{w:J→ShoreP u}{X:Chain}{G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{Ω:SectionData F}{ν:G.ColorIndex}{D':ChartRatio G}{H:Hol G}{P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{S:Prism G X.kernel g Q E}
variable {h:1/2≤R}{hD:d+1≤D} {T:Signals P Q E τ H Ω h hD}{T':Aperture G P k E τ d D R}{U V:J→ BoardU D R G} {A:Wall w 0→BoardU D R G}
section
variable (T ν D')
def echoUp (b:Offer w)(i:Wall w 0)(M:Native (Letter F)):= forward X ν D' (b.N i.a) i.i (w i.a).next.main ((prefixT ν D' T b i)*ᵥ M)
def backUp (b:Offer w)(i:Wall w 0)(M:Native (Letter F)):= ((prefixT ν D' T b i)⁻¹)*ᵥ forward X ν D' (b.N i.a) (w i.a).next.main i.i M
end
section witness
variable (b:Offer w)(he:Tights T S ν D' u) (hp:∀ i,Marvel τ (U i))(hv:∀ i,Lank (U i))
local notation "Μ" => vMatch ν D' T b U
local notation "Υ" => phase0 ν D' T b
local notation "Ⓐ" => remnant ν D' T b U
local notation "Ψ" => forward X ν D'
include he
lemma prefix_inv (i:Wall w 0) : IsUnit (prefixT ν D' T b i).det := by
    generalize hx: raceL i=n; induction n generalizing i with
    | zero=> rw [prefixT,hx,Pill.trump, firstT,turn,Matrix.det_one]; exact isUnit_one
    | succ n ih=>
      have hh:i.i>(w i.a).low:= by have he:=raceH i; omega
      let z : Wall w 1:=⟨i.a,i.i-1,by omega,by have he:=i.last; omega⟩
      have hZ:z.roof=i:= by obtain ⟨a,j,H,H'⟩:= i; unfold Wall.roof z; dsimp only; congr 1; change j>_ at hh; omega
      have hE: raceL z.low=n:= by rw [← hZ,raceUp] at hx; omega
      rw [← hZ,billP0,Matrix.det_mul]; apply IsUnit.mul _ (ih z.low hE)
      let T' := Te T ν D' (b.part z)
      let P:= ladder X ν D' (b.N z.a) z.i (w z.a|>.next.main); have hP: HasSubst P:= .of_constantCoeff_zero' (look ..)
      have hv: Pill.awake P T' * stepsT ν D' T b z=1:= by rw [← show Pill.awake P (T' * T'⁻¹)= _ from awake_mul hP T' T'⁻¹,Matrix.mul_nonsing_inv T' (recoupC (he.reads _|>.1)),awakenOne P hP] -- need unfold
      exact Matrix.isUnit_det_of_left_inverse hv
lemma back_once (i:Wall w 0)(v:Native (Letter F)): backUp ν D' T b i (echoUp ν D' T b i v)=v:= by unfold echoUp backUp; rw [forward_inverse, Matrix.mulVec_mulVec,Matrix.nonsing_inv_mul _ (prefix_inv b he i),Matrix.one_mulVec]
lemma echo_once (i:Wall w 0)(v:Native (Letter F)): echoUp ν D' T b i (backUp ν D' T b i v)=v:= by unfold echoUp backUp; rw [Matrix.mulVec_mulVec,Matrix.mul_nonsing_inv _ (prefix_inv b he i),Matrix.one_mulVec,forward_inverse]
lemma transmitted (i:Wall w 1)(M:Native (Letter F)):
    Needle.push (heights X ν D' (b.part i)) τ d (edgeBook (Υ i.roof) (echoUp ν D' T b i.roof M))=edgeBook (Υ i.low) (echoUp ν D' T b i.low M):= by
   rw [epoch_f _ (he.fair _) h (edge_crew _ _ (he.firs _|>.toBoards) (le_refl d)|>.1) d he.hh]
   unfold echoUp; rw [billP0, ← Matrix.mulVec_mulVec]; exact step_basis he (b.part i) (w i.a).next.main ((prefixT ν D' T b i.low)*ᵥ M)
omit he in
lemma prefix_start (i:Wall w 0)(ha:i.i=(w i.a).low): prefixT ν D' T b i=1:= by unfold prefixT raceL; rw [ha,Nat.sub_self,Pill.trump,firstT,turn]
lemma unique_eng (hA:∀ i,A (Wall.tip w i)=edgeBook (Υ (Wall.tip w i)) (Μ i)) (hz:∀ i:Wall w 1,A i.low=Run.route A X ν D' b.part τ d i)(i:Wall w 0) : A i=edgeBook (Υ i) (echoUp ν D' T b i (backUp ν D' T b (Wall.tip w i.a) (Μ i.a))) := by
    generalize hE:(w i.a).next.i - i.i=n; induction n generalizing i with
    | zero=>
      have hh:i.i=(w i.a).next.i:= by have he:=i.last; omega
      have ha:i=Wall.tip w i.a:= by obtain ⟨a,j,h,h'⟩:=i; unfold Wall.tip; congr 1
      -- replace both i
      rw [ha,hA, show (Wall.tip w i.a).a=i.a from rfl,echo_once b he]
    | succ n ih=>
      let z: Wall w 1:= ⟨i.a,i.i,i.first,by omega⟩
      have hh:(w z.roof.a).next.i-z.roof.i=n:= by change _-(i.i+1)=n; change (w i.a).next.i-(i.i+1)=n; omega
      change A z.low=edgeBook (Υ z.low) (echoUp ν D' T b z.low (backUp ν D' T b (Wall.tip w z.a) (Μ z.a)))
      rw [hz z]; unfold Run.route; rw [ih z.roof hh]; exact transmitted b he z (backUp ν D' T b (Wall.tip w z.a) (Μ z.a))
include hp hv
lemma reports_whole (hA:∀ i, A (Wall.tip w i)=U i)(hM:∀ i,Marvel τ (A i)∧ Lank (A i))(hT:∀ i:Wall w 1,A i.low=Run.route A X ν D' b.part τ d i)(i:J) :
    Ψ (b.N i) (w i).next.main (w i).next.i (Μ i)=(prefixT ν D' T b (Wall.tip w i))*ᵥ (Ψ (b.N i) (w i).next.main (w i).low (call H F (A (portal w i)))) := by
    let L:= A-Ⓐ; let p:= Wall.tip w i; let t:=foothold p
    have hf(i:J) : L (Wall.tip w i)=edgeBook (Υ (Wall.tip w i)) (Μ i):= by unfold L; rw [Pi.sub_apply,v_opens ν D' T b U i,hA,sub_sub_cancel]
    have he(i:Wall w 1):L i.low=Run.route L X ν D' b.part τ d i:= by
       unfold Run.route L; rw [Pi.sub_apply,Pi.sub_apply,hT i,lemma_fewer (he.fair _) h (hM _).1 (vol_p he b hp hv _|>.1),v_steps ν D' T b U i he hp hv]
    let M:= backUp ν D' T b p (Μ i)
    have hz:L t=edgeBook (Υ t) (echoUp ν D' T b t M):= unique_eng b ‹Tights T S ν D' u› hf he t
    have hU: prefixT ν D' T b t=1:=prefix_start b t rfl -- unused he?
    have hg: echoUp ν D' T b t M= Ψ (b.N i) (w i).low (w i).next.main M:= by unfold echoUp; rw [hU,Matrix.one_mulVec]; rfl
    have hc: Crop τ (Ⓐ t) H F:= v_bottom ν D' T b U p ‹Tights T S ν D' u› hp hv
    have hm: call H F (Ⓐ t)=0:= by ext j k; unfold call; rw [coeff_mk,hc.spine]; simp
    have hE: call H F (L t)= call H F (A t):= by unfold L; rw [Pi.sub_apply, ← call_grad τ (A t) (Ⓐ t) (hM _|>.1) (hM _|>.2) hc.hU hc.paid,hm, sub_zero]
    have hL: call H F (A t)=Ψ (b.N i) (w i).low (w i).next.main M:= by rw [← hE,hz,hg]; exact studyAll H (‹Tights T S ν D' u›.firs (b.part t)) _
    change _= (prefixT ν D' T b p)*ᵥ (Ψ (b.N i) (w i).next.main (w i).low (call H F (A t)))
    rw [hL,forward_inverse]; unfold M backUp; rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (prefix_inv b ‹Tights T S ν D' u› p),Matrix.one_mulVec]; rfl
end witness
section result
variable (b:Offer w)(T ν D')
-- Manufacture exact transport, no stability assumption. root step normalized. uses τ from height.
def movieP (T:Signals P Q E τ H Ω h hD) (U:J→BoardU D R G)(i:Wall w 0) := if h:i.i <(w i.a).next.i then
    let z:Wall w 1:= ⟨i.a,i.i,i.first,h⟩
    Needle.push (heights X ν D' (b.part z)) τ d (movieP T U z.roof) else U i.a
termination_by ((w i.a).next.i - i.i)
decreasing_by
    unfold Wall.roof; dsimp only; omega
-- T not included if Lean cannot infer, test
lemma movie_top (i:J) : movieP ν D' b T U (Wall.tip w i)=U i:= by rw [movieP,dif_neg (show ¬ (Wall.tip w i).i < (w (Wall.tip w i).a).next.i from Nat.lt_irrefl _)]; rfl
lemma movie_front (i:Wall w 1): movieP ν D' b T U i.low=Run.route (movieP ν D' b T U) X ν D' b.part τ d i:= by rw [movieP,dif_pos (show i.low.i<(w i.low.a).next.i from i.last)]; rfl
lemma movie_ok (he:Tights T S ν D' u)(hp:∀ i,Marvel τ (U i))(hv:∀ i,Lank (U i)) (i:Wall w 0): Marvel τ (movieP ν D' b T U i) ∧ Lank (movieP ν D' b T U i):= by
   generalize hh: (w i.a).next.i-i.i=n; induction n using Nat.strong_induction_on generalizing i with
   | h n ih=>
     rw [movieP]; split; next ht=>
        let z:Wall w 1:= ⟨i.a,i.i,i.first,ht⟩; have h' : (w z.roof.a).next.i-z.roof.i<n:= by change (w i.a).next.i-(i.i+1)<n; omega
        have hx:= ih _ h' z.roof rfl; exact ⟨crest_u (he.fair _) h hx.1,crest_l (he.fair _) h hx.1 hx.2⟩
     exact ⟨hp _,hv _⟩
end result
end YM.RG08.Taste
