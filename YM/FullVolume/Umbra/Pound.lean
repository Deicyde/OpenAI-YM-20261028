import YM.FullVolume.Umbra.Rope
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
variable {M:Bank}(I:Depot Q o x μ L C₀ K) (T:Depot Q o x μ L C₀ H){χ: Chi}(R:∀ n, Station M χ (I n) j)(P':∀ n,Station M χ (T n) j)
variable {F₀:BatchK K}{F₁:BatchK H}{k:Lotus.Wing}(hm:Rhyme F₀ F₁ k)(hJ:(J:Filter ℕ)≤ atTop) (hM: Finish J K H) (hZ:Z.Paid Q o x) (hχ: Z.χ=χ)
open Draft
set_option quotPrecheck false
include I T R P' hJ hm hM hZ hχ
section glints
variable {V:ℕ→ Config G c}(hf:∀ᶠ i in (J:Filter ℕ), Z.Viable (V i))
local notation "D"=> fun n=> Z.paints (K n) (V n)
local notation "D'"=>fun n=> Z.paints (H n) (V n)
include hf
lemma camp (w:Air f G)(i:Molecule S) : Glints J (fun n=> cups (D n) (K n).beta w * (F₀ n).premium (D n) W o.a Q.table (own i) Q.halo (kickback (D n) (K n).beta w) i) (fun n=>cups (D' n) (H n).beta w*(F₁ n).premium (D' n) W o.a Q.table (own i) Q.halo (kickback (D' n) (H n).beta w) i):=by
     unfold Leaf.premium; simp_rw [hm.left.met,hm.right.met]; split_ifs; swap; · simp only [mul_zero]; exact ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩
     let Z' n := (D n).atmos w; let V n := (D n).input (Z' n)
     let X n := (D n).enforce (2*o.a) (Z' n) ((D n).plaza (areas (K n).kin (K n).tubes 0 (D n|>.B) (k.badge S))); have he (n): X n = (D 0).enforce (2*o.a) (Z' 0) ((D 0).plaza (areas (K 0).kin (K 0).tubes 0 (D 0|>.B) (k.badge S))):= rfl
     have ht : Glints J X X:=by rw [show X=fun n=> X 0 from funext he]; exact ⟨_,tendsto_const_nhds,tendsto_const_nhds⟩
     have hp:=hm.entries J hJ V
     have h n:= Draft.mood T (H₀:=I) (j:=j) (fun i=> hχ.symm ▸ (R i).fleets.bills) hZ hM (R 0|>.N.position.le) _ hf w n (own i)
     have hx:= Glints.prods hp ht (Q:=fun x y:ℝ=>x*y) continuous_mul
     have hb:= (Frill.pears (i.erase (k.badge S)) fun e _=> Frill.bare (n:=0) (x:=(0:ℝ)) (h e)).crest
     have hz:= Glints.prods (Draft.takes I R hZ hχ hM hf w) (Glints.prods hx hb (Q:=fun x y:ℝ=>x*y) continuous_mul) (Q:=fun x y:ℝ=> x*y) continuous_mul
     refine hz.carve (hf.mono fun n hn=>?_) (hf.mono fun n hn=>?_)
     · dsimp only; unfold Leaf.paidU Leaf.fond; have hh:= (I n).laws.data; rw [shine (D n) (show Room _ S _ Z.x from hZ.1.symm ▸ hh.room) hn, kickback_home (D n) (show 0<(K n).kin.beta from (I n).laws.intake.positive) w,hm.left.met]; rfl
     dsimp only; unfold Leaf.paidU Leaf.fond; have hh:= (T n).laws.data; rw [shine (D' n) (show Room _ S _ Z.x from hZ.1.symm ▸ hh.room) hn, kickback_home (D' n) (show 0<(H n).kin.beta from (T n).laws.intake.positive) w,hm.right.met]; rfl
end glints
-- derivatives.carork
section rhythm
variable [FiniteDimensional ℝ E](hf:∀ᶠ i in (J:Filter ℕ), Z.Viable (U i p))(ht:∀ᶠ i in (J:Filter ℕ), Mode (U i) p j M.v)
local notation "D"=> fun n=> Z.paints (K n) (U n p)
local notation "D'"=>fun n=> Z.paints (H n) (U n p)
include hf ht
lemma beauty (w:Air f G)(X:Finset (Bond f))(i:Molecule S): Frill J j p (fun n y=> (F₀ n).chimes (D n) i X (U n y) M.A Q.table W o.a Q.halo (kickback (D n) (K n).beta w)) (fun n y=> (F₁ n).chimes (D' n) i X (U n y) M.A Q.table W o.a Q.halo (kickback (D' n) (H n).beta w)):=by
    unfold Leaf.chimes Leaf.floret; simp_rw [hm.left.met,hm.right.met]; split_ifs; swap; · simp only [mul_zero]; exact Frill.still _
    let d(n:ℕ):= kickback (D n) (K n).beta w; let d' n:= kickback (D' n) (H n).beta w; let u n:= (D n).atmos w
    have hv i: worldZ (D i) (K i|>.kin.beta) (d i)=u i:= kickback_home _ (I i).laws.intake.positive _; have hv' i:worldZ (D' i) (H i|>.kin.beta) (d' i)=u i:= kickback_home _ (T i).laws.intake.positive _
    let g n y z:= Polar.ember (vary (D n) (U n y)) o.a (K n).kin W Q.table (steer (D n) M.A (u n) (U n y)) ((D n).input (u n)) (course (D n) M.A (K n).beta (d n) (U n y)) (own i) Q.halo z
    let g' n y z:= Polar.ember (vary (D' n) (U n y)) o.a (H n).kin W Q.table (steer (D' n) M.A (u n) (U n y)) ((D' n).input (u n)) (course (D' n) M.A (H n).beta (d' n) (U n y)) (own i) Q.halo z
    have hQ n:Promo Q o j x M.v M.B0 M.B1 Z.χ (K n).tubes:=hχ.symm ▸ (R n).fleets.bills; let he:= (R 0).fleets.M.solid
    let m:= i.erase (k.badge S)
    have htC:= Draft.skipperY (K:=K) (H:=H) (Z:=Z) ht he w
    have hg :Frill J j p (fun n y=>∏ x∈m, g n y x) (fun n y=>∏ x∈m,g' n y x):= Frill.pears m fun b _=> Draft.hero I hQ hZ hM ht hf (fun n=> (D n).input (u n)) htC (Draft.sea I T hQ hZ hM ht hf he w) b (own i) Q.halo
    let a n y:=(F₀ n).fond (vary (D n) (U n y)) o.a (steer (D n) M.A (u n) (U n y)) ((D n).input (u n)); let a' n y:=(F₁ n).fond (vary (D' n) (U n y)) o.a (steer (D' n) M.A (u n) (U n y)) ((D' n).input (u n))
    have hc: Frill J j p a a':=by unfold a a' Leaf.fond; simp_rw [hm.left.met,hm.right.met]; exact (Frill.bare (hm.entries J hJ fun n=> (D n).input (u n))).times (Draft.mantle (Z:=Z) (K:=K) (H:=H) (U:=U) htC ((D 0).plaza (areas (K 0).kin (K 0).tubes 0 (radiusB Z.x) (k.badge S))) (2*o.a))
    refine (Draft.ship I T hQ hZ hM ht hf he w X).times (Frill.times (hc.alter ?_ ?_) (hg.alter ?_ ?_)) -- inference order
    · filter_upwards [hf,ht] with n hn hs; have hv₁:= hearts I R (F₀:=F₀) (X:=D n) hZ.1 hχ hZ.2 hn hs rfl (d n); rw [hv] at hv₁; exact hv₁.symm
    · filter_upwards [hf,ht] with n hn hs; have hv₁:= hearts T P' (F₀:=F₁) (X:=D' n) hZ.1 hχ hZ.2 hn hs rfl (d' n); rw [hv'] at hv₁; exact hv₁.symm
    · filter_upwards [hf,ht] with n hn hs; have hp:= (destiny I R (X:=D n) hZ.1 hχ hZ.2 hn hs rfl (d n) m (own i)).symm; dsimp only at hp; rw [hv] at hp; exact hp
    filter_upwards [hf,ht] with n hn hs; have hp:= (destiny T P' (X:=D' n) hZ.1 hχ hZ.2 hn hs rfl (d' n) m (own i)).symm; dsimp only at hp; rw [hv'] at hp; exact hp
end rhythm
end Umbra
end YM.ConnectedActivityE6.Lim
