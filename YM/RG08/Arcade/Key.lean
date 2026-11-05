import YM.RG08.Arcade.Stacks
/-!
# Restriction speaking through pinned Frames. Use `extracted formal graph`, not nesting raw Y’s; their level scale & horizon pinning changes. Returned coordinates below are exact after each histogram assigned.
-/
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Arcade
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Pivot Carrier Place Scores.Pages Drift Spin Taste
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ} {H:Hol G} {L : Side} {F: Frames G}
section around
-- linearity of Push even with g reset (real factors).
variable {W : StripU G L}{U:BoardU D R G}
lemma rent_sm (he: Fair W)(p:ℝ)(hp: 1/2≤R)(hx:Marvel τ U)(n): Needle.push W τ n (p • U)=p • Needle.push W τ n U := by
    unfold Needle.push; rw [filop_scale he.cm he.ct hx.cap he.odds hx.hem he.tune he.lived hp,Tall.hill_weight]
lemma rent_step (he:Fair W) (hp:1/2≤ R)(hx : Marvel τ U)(hd:d≤j) : Needle.push W τ j U=((L.val:ℝ)^(j-d)) • Needle.push W τ d U := by
    have hf: cream j U L=(L.val:ℝ)^(j-d) • cream d U L:= by
       funext e r; unfold cream reelF; simp_rw [Pi.smul_apply,Finset.smul_sum,smul_smul, ← mul_div_assoc,← pow_add,Nat.sub_add_cancel hd] -- def increase
    have hK:= veiled_whole he.cm; obtain ⟨hV,hM⟩:= creamy (L:=L) d hx.cap (fun i j=> (hx.hem i j).pens) hp he.odds
    rw [Needle.push, Needle.push, ← Tall.hill_weight]; apply congr_arg (Tall.hill W.scale); ext1 i; ext1 p; unfold filop
    rw [hf,washed_a hK he.tune hM, Pi.smul_apply,Pi.smul_apply]; exact spring_a ((washed_duty hK he.tune he.lived hM hV).2 _ _|>.pens) _ (scan_whole he.ct)
lemma gain₁ (L: Chain) (i:ℕ)(e:ℕ): (L.S.block i).val ^ e / (1:ℝ)=gain L.S (e:ℝ) (i+1) i := by rw [gain_spacing, L.S.a_step i,div_one]; have hp := (L.S.a_pos i).ne'; field_simp; simp [Real.rpow_natCast]
end around
section trial
variable {I J:Type}{ν:G.ColorIndex}{T:ChartRatio G}{X:Chain} {P:KPrices X.kernel}{g:KGate P}{Q:Lending G X.kernel}{V : Prism G X.kernel g Q E}{u:I→Windows}{w:J→ ShoreP u}
variable {S : SectionData (F.level d)}{S':SectionData (F.level j)}{h:1/2≤R}{hD:d+1≤D}{hD':j+1≤D}{B:Signals P Q E τ H S h hD}{B':Signals P Q E τ H S' h hD'}(b:Offer w)
-- anchoring offset matches $\lambda^h$. Include scale ratio in cost.
def grow_h (X:Chain)(z:ℕ)(i:Wall w 0) := gain X.S (z:ℝ) (w i.a|>.next.i) i.i
lemma grow_step (X:Chain)(z:ℕ)(i:Wall w 1) : grow_h X z i.low=(X.S.block i.i).val^z * grow_h X z i.roof := by
    unfold grow_h
    rw [gain_trans _ _ _ i.roof.i, mul_comm, show i.low.i=i.i from rfl, show i.roof.i=i.i+1 from rfl, ← show (((X.S.block i.i).val:ℝ)^z) = _ from (div_one _).symm.trans (gain₁ X _ z)]; rfl
variable (he:Tights B V ν T u)(hp:Tights B' V ν T u)(U:J→BoardU D R G)(hd:d ≤ j) (hU:∀ i,Marvel τ (U i))
include he hp hd hU
lemma horizons (i:Wall w 0): movieP ν T b B' U i=grow_h X (j-d) i • movieP ν T b B U i := by
    let K:= movieP ν T b B; let L:=movieP ν T b B'; let l(i:Wall w 0):= grow_h X (j-d) i
    suffices ∀ i:Wall w 0, Marvel τ (K U i) ∧ L U i= l i • K U i from (this i).2
    intro i; generalize hx : (w i.a).next.i - i.i=n; induction n using Nat.strong_induction_on generalizing i with
    | h n ih=>
       by_cases hv:i.i<(w i.a).next.i
       · let t: Wall w 1:= ⟨i.a,i.i,i.first,hv⟩; have ht:(w t.roof.a).next.i-t.roof.i<n:= by change (w i.a).next.i-(i.i+1)<n; omega
         obtain ⟨hb,hT⟩:= ih _ ht t.roof rfl; let Q:= heights X ν T (b.part t)
         rw [show K U i=Needle.push Q τ d (K U t.roof) from movie_front ν T B b t]; refine ⟨crest_u (he.fair _) h hb,?_⟩; rw [show L U i=Needle.push Q τ j (L U t.roof) from movie_front ν T B' b t,hT,rent_sm (he.fair _) _ h hb, rent_step (he.fair _) h hb hd,smul_smul]; apply congr_arg (· • Needle.push Q τ d (K U t.roof)); rw [mul_comm]; exact (grow_step X (j-d) t).symm
       have h:i=(Wall.tip w i.a):= by obtain ⟨a,k,h,hp⟩:=i; unfold Wall.tip; dsimp only; congr 1; change ¬ k<(w a).next.i at hv; omega
       rw [h, show K U (Wall.tip w i.a)= U i.a from movie_top ν T B b i.a, show L U (Wall.tip w i.a)= U i.a from movie_top ν T B' b i.a, show l (Wall.tip w i.a)=1 from gain_zero X.S ((j-d:ℕ):ℝ) ((w i.a).next.i), one_smul]; exact ⟨hU _,rfl⟩
local notation "Q" => (F.level d)
-- bottom projection commute. the engineering factor is not a compile artifact!
lemma reporting_p (hv:∀ i,Lank (U i))(i:Wall w 0) : let k:=gain X.S ((j-d:ℕ):ℝ) ((w i.a).next.i) i.i
    trim F hd (call H (F.level j) (movieP ν T b B' U i))= fun a=> PowerSeries.C k * call H (F.level d) (movieP ν T b B U i) a := by
    intro z; let A:= movieP ν T b B U
    obtain ⟨hA,hV⟩:= movie_ok ν T B b he hU hv i
    rw [← scopeC, horizons b he hp U hd hU i]; ext1 v; unfold call; ext k; rw [PowerSeries.coeff_mk,audit_scale H _ hA hV,PowerSeries.coeff_C_mul, PowerSeries.coeff_mk]; rfl
lemma reporting_bottom (hv:∀ i,Lank (U i))(i:J): let p:= Wall.tip w i
    let M:=backUp ν T B b p (vMatch ν T B b U i); let P:= backUp ν T B' b p (vMatch ν T B' b U i)
    trim F hd P =(fun a=> PowerSeries.C (grow_h X (j-d) (portal w i))* M a) := by
    intro p M P
    let y:=vMatch ν T B b U i; let z:=vMatch ν T B' b U i
    let A:= movieP ν T b B U; let Y:= movieP ν T b B' U; let H₁:=call (D:=D) (R:=R) H (F.level d); let H₂:= call (D:=D) (R:=R) H (F.level j); let k:=(w i).next.main; let t:= portal w i
    have hm: M= forward X ν T (b.N i) k t.i (H₁ (A t)) := by unfold M backUp; rw [show forward X ν T (b.N p.a) (w p.a).next.main p.i _=_ from reports_whole (w:=w) b he hU hv (A:=A) (movie_top ν T B b) (movie_ok ν T B b he hU hv) (movie_front ν T B b) i,mulVec_mulVec,Matrix.nonsing_inv_mul _ (prefix_inv b he p),one_mulVec]; rfl
    have hP: P= forward X ν T (b.N i) k t.i (H₂ (Y t)):= by unfold P backUp; rw [show forward X ν T (b.N p.a) (w p.a).next.main p.i _=_ from reports_whole (w:=w) b hp hU hv (A:=Y) (movie_top ν T B' b) (movie_ok ν T B' b hp hU hv) (movie_front ν T B' b) i,mulVec_mulVec,Matrix.nonsing_inv_mul _ (prefix_inv b hp p),one_mulVec]; rfl
    let c:=grow_h X (j-d) t; let L:=ladder X ν T (b.N i) t.i k
    have hv': HasSubst L:= PowerSeries.HasSubst.of_constantCoeff_zero' (look ..)
    funext v; rw [hm,hP]; change PowerSeries.subst L (Arcade.trim F hd (H₂ (Y t)) v)=PowerSeries.C c * PowerSeries.subst L (H₁ (A t) v)
    rw [show trim F hd (H₂ (Y t)) v = _ from congr_fun (reporting_p b he hp U hd hU hv t) v,PowerSeries.subst_mul hv',PowerSeries.subst_C]; rfl --] -- need helper
end trial
end YM.RG08.Arcade
