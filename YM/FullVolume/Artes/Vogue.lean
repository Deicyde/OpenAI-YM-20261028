import YM.Push.ABSOLUTE_SUMS.Basic
import YM.FullVolume.Artes.Events
/-! At specified level. strong common path in bought width; includes sums with true costs. -/
set_option autoImplicit false
noncomputable section
namespace YM.Stationary.Artes
open Function Filter Lattice RG Exterior Precision Wilson Bloch Laurent Matrix Finset Tree Supply
open Shade Beacon Flagship ConeRay Tralis WilsonStartup WilsonStartup.Change WilsonStartup.Change.Reading Next.Free Next.Free.Retort
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators Classical InnerProductSpace
variable {G: Gauge}{a:Levels G} {s: Sheet G}{L: Rolls s}{Q:PostCost L}{O:ChartRatio G}
variable {J:Horizon a}{U:Kin J O}
section assets
variable {p q:PathData G} {P:ℕ→PathData G}{w v b:ℝ}
def stillP (R S:PathData G):Prop:= (∀ i j,(R.row i j).2=(S.row i j).2)∧ (∀ i,(R.loop i).leg=(S.loop i).leg)∧ (∀ i,(R.cubic i).leg=(S.cubic i).leg)∧∀ i,(R.quartic i).leg=(S.quartic i).leg
def drag (p q:PathData G)(x:PlaqAxes)(v:ℝ)(j:ℕ):= |(p.row x j).1 - (q.row x j).1| * Real.exp (v*(p.row x j).2.length)
def kink {j:ℕ}(P Q:ℕ→Atom G j)(v:ℝ)(i:ℕ): ℝ:= Atom.budget {P i with coeff:= (P i).coeff-(Q i).coeff} v
structure Rios {p q:PathData G} (v b:ℝ): Prop where
    same : stillP p q
    row (x:PlaqAxes): SumBudget (drag p q x v) b
    loop': SumBudget (kink p.loop q.loop v) b
    three':SumBudget (kink p.cubic q.cubic v) b
    four':SumBudget (kink p.quartic q.quartic v) b
private lemma trio {m:ℕ}[NeZero m]{D:ℕ→ Cameo G m}{C:Cameo G m}(h:Gleam D C b)(hp:w<v)(e:ℝ)(he:0<e):∀ᶠ i in atTop,SumBudget (kink (ringT v (D i)) (ringT v C) w) e:=by
    have ht:= trinket h (u:=fun _=>C) (B:=‖C‖) ⟨Eventually.of_forall (fun _=>le_rfl),fun i=> tendsto_const_nhds⟩ hp; rw [sub_self,show fee v w (0:Cameo G m)=0 from ?_] at ht; swap; · simpa using (everybody hp (C:=(0:Cameo G m)) 0)
    filter_upwards [ht.eventually (ge_mem_nhds he)] with n hn; let x:= D n-C; have hZ: kink (ringT v (D n)) (ringT v C) w=(fun i=>Atom.budget (ringT v x i) w):=by
        funext i; unfold kink; apply congr_arg (fun Q=> Atom.budget Q w); apply congr_arg (fun Q=> (⟨letter (t:=m) i,Q⟩:Atom G (m+1))); ext k; change D n (i,k)/_ - C (i,k)/_=(D n (i,k)-C (i,k))/_; ring
    rw [hZ]; exact ⟨(permits hp x).1,(permits hp x).2.1,hn⟩
private lemma cove (x:PlaqAxes)(h:∀ j,Tendsto (fun i=>(P i|>.row x j).1) atTop (𝓝 (p.row x j).1))(ha:∀ j,(p.row x j).2=flag j)(hc:w<v)(hg:∀ᶠ i in atTop,(∀ j,(P i|>.row x j).2=flag j)∧ SumBudget (fun j=>|(P i|>.row x j).1| * Real.exp (v*(P i|>.row x j).2.length)) b)(e:ℝ)(he:0<e): ∀ᶠ i in atTop, SumBudget (drag (P i) p x w) e:=by
    let t:= v-w; have ht: 0<t:= sub_pos.mpr hc; let z(k:ℕ):=(b+b)*channel (-t) k
    have hp i: ∀ᶠ n in atTop, ‖(P n|>.row x i).1‖ * Real.exp (v*(p.row x i).2.length) ≤ b:= hg.mono fun n hn=>by rw [ha,←hn.1]; exact Push.AbsoluteSums.budget_single hn.2 i
    have hX : ∀ᶠ n in atTop,∀ i, ‖drag (P n) p x w i‖ ≤ z i := by
        filter_upwards [hg] with n hn i; let c:=Real.exp (v*(p.row x i).2.length)
        have hP: |(p.row x i).1| * c≤ b:= le_of_tendsto ((h i).abs.mul_const _) (hp i)
        let V:=(P n|>.row x i).1; have hz: ‖V‖*c≤ b:=by unfold c; rw [ha,← hn.1]; exact Push.AbsoluteSums.budget_single hn.2 i
        rw [Real.norm_of_nonneg (show 0≤drag (P n) p x w i by unfold drag; positivity)]; unfold z channel; rw [← ha i,show -t=w-v from (by unfold t; ring),sub_mul,Real.exp_sub]; unfold drag; rw [hn.1,← ha]; change _ ≤ (b+b)*(_/c)
        rw [show (b+b)*(Real.exp (w*(p.row x i).2.length)/c)=((b+b)/c)* Real.exp (w*(p.row x i).2.length) from (by ring)]; refine mul_le_mul_of_nonneg_right ((abs_sub _ _|>.trans ?_)) (Real.exp_pos _).le; apply (le_div_iff₀ (show 0<c from Real.exp_pos _)).2; rw [add_mul]; exact add_le_add hz hP
    have hr: Summable z:= (Beacon.coins ht).mul_left _; have hm i: Tendsto (fun n=> drag (P n) p x w i) atTop (𝓝 0):=by
        have hk := (((h i).sub_const (p.row x i).1).abs.mul_const (Real.exp (w*(flag i).length))); rw [sub_self,abs_zero,zero_mul] at hk; exact hk.congr' (hg.mono fun n hn=> by dsimp only; unfold drag; rw [hn.1]);
    have hq:= tendsto_tsum_of_dominated_convergence (f:=fun n:ℕ=>drag (P n) p x w) hr hm hX; simp only [tsum_zero] at hq
    filter_upwards [hX,hq.eventually (ge_mem_nhds he)] with n hn hL; exact ⟨fun i=> by unfold drag; positivity,Summable.of_norm_bounded hr hn,hL⟩
lemma nativity (h:Cadre Q U)(i:ℕ): ∃ (p:PathData G) (v:ℝ), p.Bounds (a.params i).clip (a.params i).width (a.params i).paths (a.clock.loopCap i) ∧ (a.params i).width < v ∧ ∀ g>0,∀ᶠ n in atTop,Rios (p:=U.path n i) (q:=p) v g:=by
    obtain ⟨R,V,hp,H,h⟩:= h.evolution i; obtain ⟨v,b,hv,hq⟩:= ‹Cadre Q U›.jac i
    obtain ⟨c,hC,hS⟩:= exists_between (lt_min hv (lt_min hp.1 (lt_min hp.2.1 hp.2.2))); rw [lt_min_iff] at hS; obtain ⟨p,Q,A',B,hA,hR,hT⟩:= h.stars
    refine ⟨R,c,H,hC,fun g hg=>?_⟩
    have hp :=h.hearth
    let W n:=U.path n i; filter_upwards [trio hA.a (hS.2.trans_le (min_le_left ..)) g hg,trio hA.b ((hS.2.trans_le (min_le_right ..)).trans_le (min_le_left ..)) g hg,trio hA.c ((hS.2.trans_le (min_le_right ..)).trans_le (min_le_right ..)) g hg,hT,hp.flit,eventually_all.mpr (fun x:PlaqAxes=>cove x (hp.ink x) (hp.here x) hS.1 ((hp.flit.and hq).mono fun n hn=>⟨hn.1 x,hn.2 x⟩) g hg)] with n ha hb hc hk hn hM
    refine ⟨⟨fun i j=>(hn i j).trans (hp.here i j).symm,fun i=> ?_,fun i=> ?_,fun i=> ?_⟩,hM,?_,?_,?_⟩
    · rw [show (U.path n _).loop=_ from hk.1, hR.1]; rfl
    · rw [show (U.path n _).cubic=_ from hk.2.1,hR.2.1]; rfl
    · rw [show (U.path n _).quartic=_ from hk.2.2,hR.2.2]; rfl
    · rw [hk.1,hR.1]; exact ha
    · rw [hk.2.1,hR.2.1]; exact hb
    rw [hk.2.2,hR.2.2]; exact hc
end assets
end YM.Stationary.Artes
