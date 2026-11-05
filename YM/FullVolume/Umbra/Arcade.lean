import YM.FullVolume.Umbra.Marys
import YM.FullVolume.Umbra.Glade
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
set_option quotPrecheck false
open Daisy Charity
include I R h
-- sum brush of differentiated logarithm. exact single derivative.T heights use `α+σ` continuity across motion not K chart.
lemma resource (hl:Sweep K):∃ f:ℕ→ (I 0).fragrances→ℝ, Sparse f ∧ ∀ i n V (x':Site c), Healthy (Pressure.temp x) (locus (F₀ n) (I n) x' i) V→ Ore V (matin (F₀ n) (I n) i χ) M.v (f n i) j:=by
    obtain ⟨q,hq⟩:= carded I R (coined M I R hl).choose_spec
    have he:Sparse (fun n (p:(I 0).ThinP)=>q n p.val):= hq.value.pull (Embedding.subtype _)
    obtain ⟨v,hv,hV⟩:= sky I R h
    let U:(n:ℕ)→ (I 0).ThinP→ℝ:=fun n i=> M.B*((R n).N.conduit.meant i.val M.k); let f n (i:(I 0).ThinP):= min (q n i.val) (U n i); let e:=(2:ℝ)^j; let g n i:= e*f n i; have hg n i: g n i ≤ (R n).N.stone i:=mul_le_mul_of_nonneg_left (min_le_right ..) (by positivity : 0≤ e); have ht n p:0≤U n p:= mul_nonneg (R n|>.N.balance) (R n|>.N.conduit.meant_nonneg M.k _)
    have hy :Sparse f:= Sparse.smaller he (fun n i=>le_min (he.value ..) (ht ..)) (fun n i=>min_le_left ..); have hb:= hy.climb (show 0≤ e by positivity)
    let k:=(2:ℝ)^j; let Q' := (I 0).smallAt; let α:=(R 0).army; have hh n:= (R n).army.purchases (R n|>.N); let y:=March.salary Q L μ M.B x j M.k
    have hR n : Ready Q' (radiusB x) (g n) (0+M.V) y M.V (1/2) :=by
       obtain ⟨ha,hz,hp,hH,hG,hQ⟩:= hh n; refine ⟨ha,hz,hp,hH,(show Sparse g from hb).value n,fun i=>?_⟩
       refine budget_mono (hQ i) (fun z=> ?_) (fun z=> ?_); · split; next he=> exact mul_nonneg ((show Sparse g from hb).value ..) (Real.exp_pos _).le
                                                              next => rfl
       -- if conditions defeq?
       split; next h=> rw [if_pos (show i∈(I n).smallAt z from h)]; exact mul_le_mul_of_nonneg_right (hg ..) (Real.exp_pos _).le
       next h=> rw [if_neg (show i∉(I n).smallAt z from h)]
    let v' n i:= e*v n i; have hS:Sparse v':= hv.climb (by positivity : 0 ≤ e)
    obtain ⟨d,u,hd,hY⟩:= raises g hR v' hS; let f' n (p:(I 0).ThinP):= g n p + d*v' n p; have hX:Sparse f':= hb.tug (hS.climb hd.le)
    have he₀ :0 ≤ 0+M.V:=by rw [zero_add]; exact α.delta.le
    have hX := profuse f' hY (I 0|>.testS) hX he₀ (fun p=> Song.crest _ p)
    let W' n (p:(I 0).fragrances):= d⁻¹ * clusters (I 0).seam (f' n) p.snd; have hl':Sparse W':= hX.climb (inv_nonneg.mpr hd.le)
    refine ⟨W',hl', fun i n V x' hp E _ _ _ F y' he' hK=>?_⟩
    let Z:= F₀ n; by_cases h: speaks (F₀ n) (I n) i
    swap; · rw [quiet (F₀ n) (I n) χ i h]; exact Brush.zi EventuallyEq.rfl (hl'.value ..) zero_le_one
    have hz: Healthy (Pressure.temp x) (I 0|>.bookFoot (.inr i)) V:=by rw [Charity.locus,if_pos h] at hp; exact hp
    let N:= (R n).N; let r:= i.fst+1; let A:=coefficient (I 0).seam i.snd; let t:=A/r.factorial
    let w p y:=leaflet (I n) χ (F y) (i.2 p); let L' p y:=libs (F₀ n) (I n) χ (F y) (i.2 p); let Y p i:=(∏ j∈univ.erase p,w j i)*L' p i; have hHV(B): Healthy (Pressure.temp x) ((I 0).smallAt (i.snd B)) V:= Finset.disjoint_of_subset_left (subset_biUnion_of_mem (fun j=> (I 0).smallAt (i.snd j)) (mem_univ _)) hz
    have hG(m): Brush j (f n (i.2 m)) 1 (w m) y':= by
        obtain h|h:= le_total (q n (i.2 m).val) (U n (i.2 m))
        · rw [show f n (i.2 m)= _ from min_eq_left h]; exact Draft.opine I R hq _ _ (hHV m) _ F y' he' hK
        rw [show f n (i.2 m)= _ from min_eq_right h]; exact (N.collective (show (I n).ThinP from i.2 m) V).2 (hHV m) _ F y' he' hK
    let a x:= f n (i.2 x); let b x:=v n (i.2 x); let c x:=(∏ j∈univ.erase x,a j)*b x *(1+(r:ℝ))^j
    have hc(x): Brush j (c x) 1 (Y x) y':=by
         have hv': Brush j (b x) 1 (L' x) y':= hV n V (i.snd x) (hHV x) E _ y' he' hK
         have hz:=(Brush.all_prod (Finset.univ.erase x) w a (fun _=>1) (fun i _=> hG i)|>.paints hv').trim
         refine hz.climb (le_of_eq ?_) le_rfl; unfold c; apply congr_arg; rw [sum_const, nsmul_eq_mul, card_erase_of_mem (mem_univ _),card_univ,Fintype.card_option,Fintype.card_fin, Nat.add_sub_cancel]; unfold r; push_cast; ring
    have hY:= (Brush.spree Finset.univ Y c zero_le_one (fun i _=> hc i)).smul t; refine hY.climb ?_ le_rfl; unfold W' clusters; let p x:= v' n (i.2 x); let fQ x:= g n (i.2 x)
    have hvx(x) : c x ≤ (∏ j∈univ.erase x, fQ j)* p x := by
         change _ ≤ _*_ ; have he: 1+(r:ℝ)≤ (2:ℝ)^r:=by rw [add_comm]; exact_mod_cast Nat.lt_two_pow_self (n:=r)
         apply le_trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) he j) (mul_nonneg (prod_nonneg fun i _=> hy.value n _) (by exact hv.value n _
           ))) (le_of_eq ?_); unfold b p v' fQ g; rw [prod_mul_distrib,prod_const,card_erase_of_mem (mem_univ _),card_univ,Fintype.card_option,Fintype.card_fin,Nat.add_sub_cancel]; unfold e; rw [←pow_mul,Nat.mul_comm r,pow_mul]; unfold r; ring
    let C' := ∏ x,f' n (i.2 x); have hC : ∑ j,c j ≤ d⁻¹*C' := by
       rw [← div_eq_inv_mul]; apply (le_div_iff₀ hd).mpr; rw [sum_mul]; refine (sum_le_sum (g:=fun x=> (∏ j∈univ.erase x, fQ j) * (d*p x)) fun x _=>?_ ).trans ?_
       · exact (mul_le_mul_of_nonneg_right (hvx x) hd.le).trans_eq (by ring)
       exact (le_add_of_nonneg_right (prod_nonneg (s:=univ) (f:=fQ) fun j _=> (show Sparse g from hb).value ..)).trans (one_mark Finset.univ fQ (fun x=>d*p x) (fun j=>hb.value ..) (fun i=>mul_nonneg hd.le (hS.value ..)))
    exact ((mul_le_mul_of_nonneg_left hC (norm_nonneg t))).trans (le_of_eq (by change |A / (r.factorial:ℝ)| * _ = d⁻¹*(|A| * C'/ (r.factorial:ℝ));rw [abs_div,abs_of_nonneg (by positivity : (0:ℝ) ≤↑(r.factorial))];ring))
end Umbra
end YM.ConnectedActivityE6.Lim
