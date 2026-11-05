import YM.FullVolume.Umbra.Arcade
import YM.FullVolume.E6.Coterie
-- one real mark among any two epoch carpets at the same stamp
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
namespace Umbra
open Lotus
open Draft
variable {Υ:ℕ→ Draft F G} {V:ℕ→ Config G c} {M:Bank}(I:Depot Q o x μ L C₀ K) (T:Depot Q o x μ L C₀ H){χ: Chi}(R:∀ n, Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
variable {F₀:BatchK K} {F₁:BatchK H}{δ δ':ℕ→ Molecule S→ℝ}{Δ Δ':ℕ} (h:Seats I (F₀:=F₀) (χ:=χ) (M:=M) (j:=j) δ Δ) (hq: Seats T (F₀:=F₁) (χ:=χ) (M:=M) (j:=j) δ' Δ') {k:Wing}(hm:Rhyme F₀ F₁ k)(hM:Mirror K H)(hJ:(J:Filter ℕ)≤ atTop) (m:Molecule S)
open Daisy Charity
variable (hl:Sweep K)(hp:Sweep H) (i:(I 0).fragrances) (s:Site c)
include I R
-- marker tallest through station. Fallback Hearth witnesses individually. need logistic.S.SO
variable {n:ℕ}
lemma flagL (hx:Hush F₀ k) : (locus (F₀ n) (I n) s i)=(locus (F₀ 0) (I 0) s i):=by unfold Charity.locus speaks; rw [hx.met n,hx.met 0];rfl
variable {n:ℕ} {B:BudgetPoint}
include T hq P' hm h
lemma flagV (n:ℕ): (locus (F₁ n) (T n) s i)=(locus (F₀ 0) (I 0) s i):=by unfold Charity.locus speaks; rw [hm.left.met 0,hm.right.met n]; rfl
section continuities
variable [FiniteDimensional ℝ E]
include hl hp hM hJ
lemma marchL (he:∀ n,Healthy (Pressure.temp x) (locus (F₀ 0) (I 0) s i) (U n p))(hb:∀ n, Mode (U n) p j M.v): Frill J j p (fun n z=> matin (F₀ n) (I n) i χ (U n z)) (fun n z=>matin (F₁ n) (T n) i χ (U n z)):=by
     by_cases hc: speaks (F₀ 0) (I 0) i
     swap; · have hu n: ¬ speaks (F₀ n) (I n) i:= by intro h; apply hc; unfold speaks at *; rw [hm.left.met] at *; exact h
             have hv n: ¬ speaks (F₁ n) (T n) i:= by intro h; apply hc; unfold speaks at *; rw [hm.right.met] at h; rw [hm.left.met]; exact h
             simp_rw [fun n=> quiet (F₀ n) (I n) χ i (hu n),fun n=> quiet (F₁ n) (T n) χ i (hv n)]; exact Frill.still _
     have ht n:Healthy (Pressure.temp x) (perf (I 0) i) (U n p):=by have h:=he n; rw [Charity.locus,if_pos hc] at h; exact h
     have hv(k:Option (Fin i.1))(n):Healthy (Pressure.temp x) ((I 0).smallAt (i.2 k)) (U n p):= Finset.disjoint_of_subset_left (Finset.subset_biUnion_of_mem ((I 0).smallAt ∘ i.snd) (mem_univ k)) (ht n)
     exact (Frill.still (coefficient (I 0).seam i.snd/(i.fst+1).factorial)).times (Frill.buds Finset.univ (fun k _=> (Frill.pears (Finset.univ.erase k) (fun x _=> Draft.levers I T R P' hl hp hM hJ (i.2 x) (hv x) hb)).times ( escortG I T R P' h hq hm hM hJ _ (hv k) hb)))
end continuities
omit T P' hq hm
variable (z: (I 0).fragrances→ RegularAddress c) (hT:B.threshold=Pressure.temp x)(hS:B.order≤j)
include hl h hT hS
lemma phasing (hx:Hush F₀ k) (hz:∀ i,(z i).support= locus (F₀ 0) (I 0) s i)(hf:∀ i n,B.Regular (z i).support (matin (F₀ n) (I n) i χ)): PulseWise B z (fun n i=> matin (F₀ n) (I n) i χ):=by
    obtain ⟨Y,H⟩:= (Set.finite_range (fun x:Site c×Site c=> 1+(separation x.1 x.2:ℝ))).bddAbove; have hh (y z:Site c):1+(separation y z:ℝ) ≤ Y:=H ⟨(y,z),rfl⟩; have hv:1≤Y:=by simpa using hh 0 0
    obtain ⟨v,hp,V⟩:= resource I R h hl; exact ⟨fun i n=>hf n i,_,hp.climb (show 0 ≤ Y^(B.power*j) by positivity),fun n i=> lyre I R hh B hT hS (hp.value ..) ⟨_,(z i).anchor⟩ (hf i n) (fun U hu=>V i n U s (show _ from (flagL I R i s hx).symm ▸ (hz i ▸ hu))) _⟩
include T P' hq hm hM hp
lemma swan (hz:∀ i,(z i).support=locus (F₀ 0) (I 0) s i)(hf:∀ n i,B.Regular (z i).support (matin (F₀ n) (I n) i χ))(hu:∀ n i,B.Regular (z i).support (matin (F₁ n) (T n) i χ)): Canopy B z (fun n i=> matin (F₀ n) (I n) i χ) (fun n i=>matin (F₁ n) (T n) i χ):=by
    obtain ⟨Y,H'⟩:= (Set.finite_range (fun x:Site c×Site c=> 1+(separation x.1 x.2:ℝ))).bddAbove; have hh (y z:Site c):1+(separation y z:ℝ) ≤ Y:=H' ⟨(y,z),rfl⟩; have hv:1≤Y:=by simpa using hh 0 0
    have h₁ n i:(z i).support=locus (F₀ n) (I n) s i:= (hz i).trans (flagL I R i s hm.left).symm; have h₂ n i:(z i).support=locus (F₁ n) (T n) s i:= (hz i).trans (flagV I T R P' h hq hm i s n).symm
    refine ⟨phasing I R h hl _ z hT hS hm.left hz (fun i n=> hf n i), phasing T P' hq hp s z hT hS hm.right (h₂ 0) (fun i n=> hu n i),fun i b he=> ?_⟩
    let Z:=(z i).support; obtain ⟨v,hv',hV⟩:= resource I R h hl; obtain ⟨d,he',hD⟩:= resource T P' hq hp
    let f n:= matin (F₀ n) (I n) i χ; let g n:= matin (F₁ n) (T n) i χ
    have hx : Nonempty ({x':Config G c|Healthy (Pressure.temp x) Z x'}:Set _):=⟨⟨1,hT ▸ CouplingShape.clear_one B Z⟩⟩
    have ht n U(h:Healthy (Pressure.temp x) Z U):∃ c d, Ore U (f n) M.v c j∧ Ore U (g n) M.v d j:=⟨_,_,hV i n _ s (h₁ n i ▸ h),hD i n _ s (h₂ n i ▸ h)⟩
    let C:= Y^(B.power*j); have ha:0<C:=by unfold C; positivity
    have hG (k:ℕ)(hi:k≤j)(V:ℕ→ (Fin k→ℝ)→ Config G c)(hU:∀ i,Mode (V i) 0 j M.v)(hw:∀ n,Healthy (Pressure.temp x) Z (V n 0)): Tendsto (fun n=>iteratedFDeriv ℝ k (f n∘V n) 0-iteratedFDeriv ℝ k (g n ∘V n) 0) atTop (𝓝 0):=(tendsto_iff_ultrafilter ..).mpr fun J hj=> ((marchL I T R P' h hq hm hM hj hl hp i s (fun n=> h₁ 0 i ▸ hw n) hU).feel k hi).shrank
    filter_upwards [Lim.boots hx (R 0|>.N.position.le) ht hG _ (show 0<b/C from div_pos he ha)] with n hn
    have hK:= lyre I R hh B hT hS (div_pos he ha|>.le) ⟨_,(z i).anchor⟩ (CouplingShape.reg_sub (hf n i) (hu n i)) (fun U hu=> hn U hu) (z i).site
    rw [show Y^(B.power*j)*(b/C)=b by change C*(b/C)=b; field_simp] at hK; exact hK
end Umbra
end YM.ConnectedActivityE6.Lim
