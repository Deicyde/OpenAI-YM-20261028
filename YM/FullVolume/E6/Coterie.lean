import YM.FullVolume.E6.Azure
/-! E6 Layout steps full volume.Epoch. Keep Records by exact tags.Canvas.Read.F. -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Lim
open Function Filter Set Lattice RG Pressure Pressure.Tube Tree Wilson Finset MeasureTheory
open Shell Coat SliceRows Pulse Mask Raw Matter Pond
open Push Push.AbsoluteSums Gas Ursell Trees Multiple Letter OmitClusters RG Shoot Precision SectorMeasure Oriented Reserves
open AnalyticBridge VerifiedReset Collection Quotes UVNext Next.Scheduling Org
open Extra.Iteration PhysicalNext.Repeat Greenbelt Match Song Refrain
open Blaze Blaze.March Captain Silica Height Brim Time Supply Input Testing PriceCompiler Opera
open UVNext.CouplingReset Animals Progress.DirectedRecipe Ovens
open Stationary Stationary.Shade Stationary.Beacon Laurent Exterior Bloch
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {P : Teller G} {S : StepData c f} {F : Forest S.ratio}
open Matrix Window Progress.StationaryScenes Green Census Control Flux FullVolume.Shadow
open Gate Frond Vine Mask
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E] {φ: Filter ℕ}{J: Ultrafilter ℕ}{Q:ConnectedActivityE6.Target G P}{W x μ C₀ a b e ℓ v :ℝ}{o:Target.Order G W}
    {Λ: Era G S}{U:ℕ→ E→ Config G c}{Z: Draft F G} {K H:ℕ→ Epoch Λ}{j:ℕ}{p:E}
open FullVolume.Neptune Flux Shield Eider Packets Polar
variable {ι κ:Type}
structure PulseWise (P:BudgetPoint)(A:ι→RegularAddress c)(F:ℕ→ι→ Config G c→ℝ):Prop where
    chart:∀ n i,P.Regular (A i).support (F n i)
    sup :∃ v:ℕ→ ι→ℝ,Sparse v∧∀ n i,P.supBounds (A i).site (A i).support (F n i) (v n i)
structure Canopy (P:BudgetPoint)(A:ι→RegularAddress c)(F H:ℕ→ι→ Config G c→ℝ): Prop where
    a : PulseWise P A F
    b : PulseWise P A H
    sails : ∀ i b,b>0→∀ᶠ n in atTop, P.supBounds (A i).site (A i).support (F n i - H n i) b
structure Vented (F:ℕ→ι→ Config G c→ℝ): Prop where
    sup:∃ v:ℕ→ι→ℝ,Sparse v∧∀ n V i, ‖F n i V‖ ≤ v n i
structure Angel (F H:ℕ→ι→ Config G c→ℝ):Prop where
    a: Vented F
    b: Vented H
    sails:∀ i b,b>0→∀ᶠ n in atTop,∀ U,‖F n i U-H n i U‖≤b
namespace Draft
variable {M:Bank}(I:Depot Q o x μ L C₀ K)(T:Depot Q o x μ L C₀ H){χ:Chi}(R:∀ n,Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)(h:Sweep K)(hp:Sweep H)(hM:Mirror K H)
variable {Y:ℝ}(hx:∀ x y:Site c,1+(separation x y:ℝ)≤Y)(B:BudgetPoint) (hT:B.threshold=Pressure.temp x) (hS:B.order≤ j)
include hx I R B hT hS
lemma lyre {s:Support c} {V: Config G c→ℝ} (hn:0≤b) (v:∃ i:Site c,i∈s)(hk:B.Regular s V)(he:∀ U,Healthy (Pressure.temp x) s U→ Ore U V M.v b j)(i:Site c): B.supBounds i s V (Y^(B.power*j)*b):=by
    have hh:1≤Y:=le_trans (le_add_of_nonneg_right (show 0 ≤ (separation i i:ℝ) from Nat.cast_nonneg _)) (hx i i); let H:=(R 0).N
    have ha : Sailor G B.threshold M.q j:= ⟨fun c _ hb => H.weigh.stroke c _ (hb.trans (hT.trans_le H.talent))⟩
    refine ⟨mul_nonneg (pow_nonneg (by linarith) _) hn,fun U hu l hl hv=>?_⟩; exact costsD hk.sites ha (H.income) i b H.near (he U (hT ▸ hu)) (fun i _=> hx i _) hh l (hl.trans hS) hv
omit hx
include h
lemma stanza (A:(I 0).fragrances→RegularAddress c) (he:∀ z,(A z).support=perf (I 0) z): PulseWise B A (fun n i V=> stream (I n) χ V i):=by
    obtain ⟨Y,H⟩:= (Set.finite_range (fun x:Site c × Site c=> 1+(separation x.1 x.2:ℝ))).bddAbove
    have hx (y z:Site c):1+(separation y z:ℝ) ≤ Y:=H ⟨(y,z),rfl⟩
    have hv:1≤Y:=by simpa using hx 0 0
    have hn n p:B.Regular (A p).support (fun V=> stream (I n) χ V p):= he p|>.symm ▸ ((R n).N.gloryBudget p B hT hS).2.1
    obtain ⟨v,hp,hv'⟩:= divan I R h; refine ⟨hn,⟨_,hp.climb (show 0≤Y^(B.power*j) by positivity),fun n i=> lyre I R hx B hT hS (hp.value ..) ⟨_, (A i).anchor⟩ (hn n i) (fun U hu=> hv' i n U (he i ▸ hu)) _⟩⟩
include hp hM T P'
lemma concordance (A:(I 0).fragrances→RegularAddress c) (he:∀ z,(A z).support=perf (I 0) z): Canopy B A (fun n i V=> stream (I n) χ V i) (fun n i V=>stream (T n) χ V i):=by
    have hx:=stanza I R h B hT hS A he; have hg:= stanza T P' hp B hT hS A he; refine ⟨hx,hg,fun i t ht=>?_⟩
    obtain ⟨Y,H⟩:= (Set.finite_range (fun x:Site c × Site c=> 1+(separation x.1 x.2:ℝ))).bddAbove
    have hh (y z:Site c):1+(separation y z:ℝ) ≤ Y:=H ⟨(y,z),rfl⟩
    have hv:1≤Y:=by simpa using hh 0 0
    let g:=fun n (U:Config G c)=> stream (I n) χ U i; let f:=fun n (U:Config G c)=>stream (T n) χ U i; let p:= perf (I 0) i
    have hz n (U) (hi:Healthy (Pressure.temp x) p U): ∃ a b,Ore U (g n) M.v a j∧ Ore U (f n) M.v b j:=⟨_,_, ((R n).N.permitAverage i).2.2.2.2 U hi, ((P' n).N.permitAverage i).2.2.2.2 U hi⟩
    have hf:Healthy (Pressure.temp x) p (1:Config G c):= hT ▸ CouplingShape.clear_one B p
    let T':=Y^(B.power*j); have hF:0<T':=by unfold T'; positivity
    have hG (k:ℕ)(hi:k≤j)(V:ℕ→ (Fin k→ℝ)→ Config G c)(he:∀ i, Mode (V i) 0 j M.v)(hV:∀ i,Healthy (Pressure.temp x) p (V i 0)): Tendsto (fun i=>iteratedFDeriv ℝ k (g i ∘ V i) 0- iteratedFDeriv ℝ k (f i ∘ V i) 0) atTop (𝓝 0):=(tendsto_iff_ultrafilter ..).mpr fun J hj=> ((Draft.candle I T R P' h hp hM hj i hV he).feel k hi).shrank
    filter_upwards [Lim.boots (X:=Healthy (Pressure.temp x) p) (show Nonempty _ from ⟨⟨1,hf⟩⟩) (R 0|>.N.position.le) hz hG _ (show 0<t/T' from div_pos ht hF)] with n hn
    have hd:= lyre I R hh B hT hS (div_pos ht hF|>.le) ⟨_,(A i).anchor⟩ (CouplingShape.reg_sub (hx.chart n i) (hg.chart n i)) (fun U hu=>hn U (show Healthy _ (perf (I 0) i) U from he i ▸ hu)) (A i).site;  rw [show Y^(B.power*j)*(t/T')=t by change T'*(t/T')=t; field_simp] at hd; exact hd
omit B hT hS in
lemma cardigan : Angel (fun n (p:(I 0).Chainbook) V=> (I n).smilesPool χ V p) (fun n (p:(I 0).Chainbook) V=> (T n).smilesPool χ V p):=by
    obtain ⟨u,hu,U⟩:= tassels I R h; obtain ⟨v,hv,V⟩:= tassels T P' hp
    exact ⟨⟨u,hu,U⟩,⟨v,hv,V⟩,fun i t ht=> recover (fun V=> (tendsto_iff_ultrafilter ..).mpr fun J hj=> (spirits I T R P' h hp hM hj V i).shrank) _ ht⟩
end Draft
end YM.ConnectedActivityE6.Lim
