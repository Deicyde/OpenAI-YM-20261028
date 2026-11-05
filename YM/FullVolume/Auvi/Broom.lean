import YM.FullVolume.Table.Vars
import YM.FullVolume.Auvi.Entries
import YM.FullVolume.Renew.Ready
import YM.FullVolume.Sym.Chill
/- point of departure -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lark
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open ConnectedActivityE6 Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration Greenbelt Match Song Refrain
open ConnectedActivityE6.Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Beacon Stationary.Shade Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G:Gauge}{c f:Side}{X:Metals G}{D:Rolls X.p}{A:Alloy X D}{R:Roost.Factor A}
open Rain Pane Roof ConnectedActivityE6.Lim FullVolume FullVolume.Shadow FullVolume.Neptune
open Urns
namespace Trill
private lemma pebble {E: Type}[SeminormedAddCommGroup E](C:ℝ)(F:E→ℕ→ Config G c→ℝ)(h:∀ f:E,∃ b:ℕ→ℝ,SumBudget b (C*‖f‖)∧∀ i y,‖F f i y‖≤ b i) (hs:∀ f g:E, F (f-g)=F f-F g) :∃ B:E→ℕ→ℝ,(∀ f:E,SumBudget (B f) (C*‖f‖)∧∀ i y,‖F f i y‖≤ B f i)∧∀ f g i,B f i ≤ B (f-g) i+B g i:=by
    let Sx (f:E)(i:ℕ): Set ℝ:= Set.range (fun x:Config G c=>‖F f i x‖)
    let B(f:E)(i:ℕ):= sSup (Sx f i)
    choose a ha H using h
    have hn f i: Sx f i|>.Nonempty:=Set.range_nonempty _; have hb f i:a f i∈upperBounds (Sx f i):=by rintro _ ⟨x,rfl⟩; exact H ..
    have he(f:E)(i x):‖F f i x‖≤B f i:=le_csSup ⟨_,hb ..⟩ ⟨x,rfl⟩
    refine ⟨B,fun f=> ⟨budget_mono (ha f) (fun i=>(norm_nonneg _).trans (he f i 1)) (fun i=> csSup_le (hn f i) (hb f i)),he f⟩,fun f g i=>csSup_le (hn _ _) ?_⟩
    rintro _ ⟨x,rfl⟩; have he':F f i x=F (f-g) i x+F g i x:=by rw [hs]; exact (sub_add_cancel _ _).symm
    dsimp only; nth_rw 1 [he']; exact (norm_add_le ..).trans (add_le_add (he ..) (he ..))
lemma plumage {E: Type}[SeminormedAddCommGroup E]{A B:ℕ→ E}(hA:CauchySeq A)(hB:CauchySeq B)(he:Tendsto (fun n=> A n-B n) atTop (𝓝 0))(C:ℝ)(hc:0<C)(F:E→ℕ→ Config G c→ℝ)(h:∀ f:E,∃ b:ℕ→ℝ,SumBudget b (C*‖f‖)∧∀ i y,‖F f i y‖≤ b i) (hs:∀ f g:E,F (f-g)=F f-F g): Angel (fun n=> F (A n)) (fun n=> F (B n)):=by
    obtain ⟨q,hq,H⟩:= pebble C F h hs
    have hz {A:ℕ→E}(h:CauchySeq A):Vented fun n=>F (A n):=by
          obtain ⟨D,hD⟩:= isBounded_iff_forall_norm_le.mp h.isBounded_range; let v(n):= q (A n)
          refine ⟨v,⟨⟨C*D,fun i=> budget_loosen (hq (A i)|>.1) (mul_le_mul_of_nonneg_left (hD _ (Set.mem_range_self _)) hc.le)⟩,fun ε hp=>?_⟩,fun n x i=> (hq _).2 i x⟩
          let t:= (ε/2)/C; obtain ⟨N,hN⟩:= Metric.cauchySeq_iff.mp h t (div_pos (half_pos hp) hc)
          have hp i: Sparse fun _=> q (A i):= Sparse.constant (hq _).1.2.1 (hq _).1.1
          choose T hT using fun (i:ℕ)=> (hp i).stalls _ (half_pos ‹0<ε›)
          refine ⟨(Finset.range (N+1)).biUnion T,fun n U hu=> ?_⟩; have hf k(hk:k≤N): ∑ i∈U, q (A k) i≤ε/2:= hT k 0 _ (Disjoint.mono_left (subset_biUnion_of_mem T (Finset.mem_range.mpr (by omega))) hu)
          by_cases hx:n≤ N
          · exact (hf n hx).trans (half_lt_self ‹0<ε›|>.le)
          have hd:= hN n (by omega) N le_rfl; rw [dist_eq_norm] at hd
          apply le_trans (Finset.sum_le_sum (g:=fun i=> q (A n-A N) i+ q (A N) i) fun _ _=> H ..)
          rw [sum_add_distrib]; exact (add_le_add ((budget_sum (hq (A n-A N)|>.1) U).trans (by rw [mul_comm]; exact (le_div_iff₀ hc).mp hd.le)) (hf N le_rfl)).trans_eq (add_halves _)
    refine ⟨hz hA,hz hB,fun i t ht=>?_ ⟩; have hX:=he.norm.const_mul C; rw [norm_zero,mul_zero] at hX
    filter_upwards [hX.eventually (ge_mem_nhds ht)] with n hn V; rw [← show F (A n-B n) i V=F (A n) i V-F (B n) i V by rw [hs]; rfl]; exact (hq _|>.2 i _).trans ((budget_single (hq _|>.1) i).trans hn)
private lemma buy_tot (b:ℕ→ℝ)(hb:∀ i,0≤b i)(v:Site c→ℕ→ℝ)(w:ℝ)(he:∀ x:Site c,SumBudget (v x) w)(hh:∀ k,b k≤∑ x,v x k): SumBudget b (Fintype.card (Site c)*w):=by
    apply budget_of_sum hb; intro S; apply le_trans (sum_le_sum fun j _=> hh j); rw [sum_comm]; simpa only [sum_const,card_univ,nsmul_eq_mul] using sum_le_sum (s:=univ) (g:=fun _=>w) (fun i _=>budget_sum (he i) S)
variable {P:Urns.Price G c}
private lemma C_pos (z:ℝ)(c:Side)(he:0<z):0<(Fintype.card (Site c):ℝ)*z:=by positivity
variable {T H:ℕ→ Show P}(hp:CauchySeq T)(hH:CauchySeq H)(ht:Tendsto (fun n=> T n-H n) atTop (𝓝 0))
include hp hH ht
lemma hockey : Angel (fun n=> (T n|>.proper.K)) (fun n=> H n|>.proper.K):=by
    refine plumage hp hH ht (Fintype.card (Site c)*P.k) (C_pos _ _ P.k0) (fun x=> x.proper.K) (fun f=> ?_) (fun _ _=> rfl)
    let R:= f.proper
    obtain ⟨b,hb,h⟩:= (Show.budget f ‖f‖).mp le_rfl|>.2.2.2; let v x i:= if x ∈ (R.forced i).support then P.p.mass (R.forced i).support (b i) else 0
    refine ⟨b,budget_loosen (buy_tot b (fun i=>(hb i).1) v _ h fun j=>?_)  ?_,fun i=> (hb i).2⟩
    · obtain ⟨x,hx⟩:= (R.forced j).inventory_ne.mono (R.forced j).inventory_sup; refine (P.p.loMass _ _ (hb j).1).trans ((show _=v x j from Eq.symm (if_pos hx))|>.trans_le (single_le_sum (fun k _=> (h k).1 j) (Finset.mem_univ (α:=Site c) x)))
    ring_nf; rfl
lemma gloves : Angel (fun n i U=> (T n|>.proper).regularOccurrence P.p i U) (fun n i U=> (H n|>.proper).regularOccurrence P.p i U):=by
    refine plumage hp hH ht (Fintype.card (Site c)*P.b) (C_pos _ _ P.b0) (fun f=> f.proper.regularOccurrence P.p) (fun f=>?_) ?_
    · obtain ⟨b,hb,h⟩:= (Show.budget f ‖f‖).mp le_rfl|>.2.2.1; let A:= f.proper; let v(x:Site c)(j:ℕ):=if (A.reg j).site=x then P.p.mass (A.reg j).support (b j) else 0
      have hk:= buy_tot b (fun j=>(hb j).1) v _ h fun k=> by simp only [v,sum_ite_eq,Finset.mem_univ, if_true]; exact P.p.loMass _ _ (hb k).1
      rw [mul_comm ‖f‖ P.b,←mul_assoc] at hk; refine ⟨b,hk,fun i x=>?_⟩; unfold Activities.regularOccurrence; by_cases hX:Healthy P.p.threshold (f.proper.reg i).support x
      · rw [masked_eq _ _ _ _ hX]; exact (hb i).2 _ hX [] (Nat.zero_le _) (by simp)
      rw [masked_ne _ _ _ _ hX,norm_zero]; exact (hb i).1
    intro f g; ext i U; dsimp only [Pi.sub_apply]; unfold Activities.regularOccurrence; change masked _ (f.proper.reg i).support _ _= masked _ (f.proper.reg i).support _ _- masked _ (f.proper.reg i).support _ _
    unfold masked; by_cases he:Healthy P.p.threshold (f.proper.reg i).support U; all_goals simp [Set.indicator, he] <;> rfl --; rfl; rw [sub_zero]
end Trill
end YM.PhysicalNext.Repeat.Lark
