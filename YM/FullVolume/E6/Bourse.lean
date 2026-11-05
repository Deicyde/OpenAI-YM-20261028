import YM.FullVolume.E6.Gest
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
structure Sweep (K:ℕ→ Epoch Λ):Prop where
    paidE : ∃ f:ℕ→ℕ→ℝ,Sparse f ∧ ∀ i k U, |(K i).kin.activities.regularOccurrence Λ.p k U| ≤ f i k
    paidK : ∃ f:ℕ→ℕ→ℝ,Sparse f ∧ ∀ i k U, |(K i).k k U| ≤ f i k
lemma expandsP (j:ℕ){B:ℝ}(hB:0≤B):∃ C:ℝ,0≤C ∧ ∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E](f:E→ℝ)(w x), w≤B→ Brush j w 1 f x → Brush j (C*w) 1 (fun x=>Real.exp (f x)-1) x:=by
   let g(x:ℝ):=Real.exp x-1
   obtain ⟨v,hv,hg⟩:= Brush.compact (k:=j) (s:=Set.Icc (-B) B) (f:=g) isCompact_Icc (fun i hi=> Real.contDiff_exp.contDiffAt.sub contDiffAt_const)
   obtain ⟨A,hA,h⟩:= Brush.expands j
   let C:=j.factorial*v*(1+((1+B)*1))^j; have hC:0≤C:=by unfold C; positivity
   refine ⟨A+C,by positivity,fun E _ _ f w x hx he=>?_⟩
   by_cases hz:w ≤ 1
   · refine (h E x w 1 f he hz).climb (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC) he.nonneg) le_rfl
   apply (((he.pine (hg _ (abs_le.mp (he.bound.trans hx)))).climb le_rfl (mul_le_mul_of_nonneg_right (add_le_add_right hx _) zero_le_one)).trim).climb _ le_rfl
   exact (le_add_of_nonneg_left hA).trans (le_mul_of_one_le_right (by positivity : 0≤ A+C) (not_le.mp hz|>.le))
lemma tariffC (H₀:∀ n,Cash W x μ L Q o C₀ (K n).tubes (K n).kin) (A:Stores S)(v:ℝ): ∃ C:ℝ, 0≤C∧∀ n, steamP S (Q.costs L μ (K n).beta x v) A ≤ C:=by
   let b:=betaF G x S.patch.L
   obtain ⟨C,hC⟩:= (isCompact_Icc (a:=b/2) (b:=2*b)).bddAbove_image (f:=fun t=> steamP S (Q.costs L μ t x v) A) (by unfold steamP Target.costs Buy.quote; dsimp only; unfold Packets.income Grant.credit; fun_prop)
   exact ⟨|C|,abs_nonneg _,fun n=>(hC (Set.mem_image_of_mem _ (show (K n).beta∈Set.Icc _ _ from (H₀ n).laws.intake.window))).trans (le_abs_self _)⟩
abbrev Depot (Q:ConnectedActivityE6.Target G P) (o: Target.Order G W) (x μ:ℝ)(L: Side)(C:ℝ)(K: ℕ→ Epoch Λ):=∀ n,Cash W x μ L Q o C (K n).tubes (K n).kin
variable (M:Bank) (H₀: Depot Q o x μ L C₀ K) {χ:Chi}(Y:∀ n,Station M χ (H₀ n) j)
set_option quotPrecheck false
local notation "R"=> radiusB x
local notation "w" => Q.halo
-- brush for all paid inputs. supports exact. HOLDING U.
structure Coins (M:Bank)(Q:ConnectedActivityE6.Target G P)(o:Target.Order G W)(χ:Chi)(j:ℕ)(x:ℝ)(K:ℕ→Epoch Λ)(D:ℕ→Head S→ℝ):Prop where
    silver: Sparse D
    force:∀ n (F:Forest S.ratio) (X:Coat (K n).tubes F), X.x=x → X.width=o.K → X.χ=χ → X.manifest → ∀ l z i, |X.vertex (K n).kin Q.table W o.a l Q.halo z i| ≤ D n i
    regular:∀ n (F:Forest S.ratio) (X:Coat (K n).tubes F), X.x=x → X.width=o.K→ X.χ=χ→ X.manifest→∀ l (z:Air f G) i, Healthy (Pressure.temp x) (areas (K n).kin (K n).tubes Q.halo (radiusB x) i) X.V →∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](V:E→ Config G c)(p:E), V p=X.V → Mode V p j M.v →
        let u:=worldZ X (K n).beta z
        Brush j (D n i) 1 (fun y=> Polar.ember (vary X (V y)) o.a (K n).kin W Q.table (steer X M.A u (V y)) (X.input u) (course X M.A (K n).beta z (V y)) l Q.halo i) p
lemma boundCone (z: Bank) (H: Depot Q o x μ L C₀ K) (Y:∀ n,Station z χ (H n) j):∃ v:ℝ,1≤v∧∀ n (F:Forest S.ratio)(X:Coat (K n).tubes F),X.x=x → X.width=o.K → X.χ=χ → X.manifest → ∀ (p:Air f G) (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](V:E→ Config G c)(s:E), V s=X.V → Mode V s j z.v →∀ D:Support c, Brush j v 1 (fun y=> (vary X (V y)).enforce (2*o.a) (steer X z.A (worldZ X (K n).beta p) (V y)) (X.plaza D)) s:=by
   let v0:(Support c)→ℝ:=fun D=> 1*(1+(z.W*coverNumber R D))^j
   obtain ⟨C,hC⟩:= (Set.finite_range v0).bddAbove
   refine ⟨max 1 C,le_max_left ..,fun n F X hx hz hχ he p E _ _ _ V s hs hv D=>?_⟩
   refine (((Y n).fleets.curtain F X hx hz hχ he E V s hs hv p).1 D D (Finset.Subset.refl _)).trim.climb ?_ le_rfl
   unfold Coat.B; rw [hx]; exact (hC (mem_range_self (f:=v0) D)).trans (le_max_right ..)
end YM.ConnectedActivityE6.Lim
