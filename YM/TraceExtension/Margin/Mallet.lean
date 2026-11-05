import YM.TraceExtension.Margin.Pillar
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Margin
open Function Filter Lattice Matrix Precision Laurent Labels Source RG Wilson StressFlux
open Finset Kits Pressure Terrace Terrace.Glade Work Further.PhysicalPeriodLimitF933
open Shunt Wicket Perfect Turret Weir Extra.Histories Next.Foundations Planned.PrimaryIntegral295 Place
open scoped BigOperators Topology Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{s:Side}{Φ:Peat G s}{H:Hol G}
open Zn
variable {F:Frame G 4}{Z:Frame G 5}{n:Side}{t:ℝ}{R:Rep G n}{J:Dart G n}
open AnalyticBridge AnalyticBridge.SectorAffine Extra.Iteration WardBin WardBin.Wheels Next.Fluctuations Planned.AtomRegular.Foliage Work.E01 Push.Uniform
-- shear & square-only.
abbrev azure (M:Bool):Fin 3→ℝ:= if M then ![0,1/4,0] else ![0,0,1]
def Toca (c:Bool)(i j:Axis) : Peat G n:= if c then (if i=j then (1/4:ℝ) • ∑ a:Axis, ∑ j:Axis, bornPair 0 a a j else 0) else (if i=j then 0 else ∑ a:Axis,bornPair 0 i j a)
def Plint (G:Gauge)(n:Side)(t:Bool): Sway G n:= fun i j x=> rj x (Toca t i j)
lemma born_house (k:ℕ)(d:ℝ)(hd:0≤ d)(G:Gauge):∃ Y:ℝ,0 ≤ Y ∧ ∀ (n:Side)(i j b:Axis), Splendor (bornPair (G:=G) 0 i j b) (sprout (0:Site n) 4) k Y d:=by
   let P(v):= travelCost G k 4 v ; let z(v):=curvatureCost G*P v; let L:= innerSL ℝ (E:=G.Color); let f(Y:ℝ):= ((2:ℝ)^k)* ‖L‖* z Y*z Y
   refine ⟨max 0 (f d),le_max_left ..,fun n i j b=>?_⟩;
   have ht (v:ℝ)(X:Type)[NormedAddCommGroup X][NormedSpace ℝ X](U:X→ Config G n)(x:X)(hp:∀ i,Allows k (fun y=>G.mat (U y i)) x v): Allows k (bornPair (G:=G) 0 i j b ∘ U) x (f v):=by
       have hz (a:Axis):Allows k (tulip 0 a b ∘ U) x (z v):= curvature_price (U:=fun i=> travel (U i) 0 (square a b)) (M:=P v) (travel_jets hp _ (by simp[square]))
       exact (hz i).bilinear L (hz j) le_rfl
   have hL (a:Axis):LocalOn (Turret.sprout (0:Site n) 4:Set (Site n)) (tulip (G:=G) (0:Site n) a b):=by
      have he(x:Site n)(h:x∈ visits (0:Site n) (Lattice.square a b)):x∈ Turret.sprout 0 4:= halo_spec.mpr ⟨_,mem_singleton_self _,Shapes.visits_dist _ x (Lattice.square a b) h⟩
      intro U V hp; exact congr_arg G.curvature (travel_local (0:Site n) _ U V (fun i hi hz=> hp i (he _ hi) (he _ hz)))
   refine ⟨(born_win ..).1,fun U V h=> congr_arg₂ (inner ℝ) (hL i U V h) (hL j U V h),fun a v=> ?_, fun v=> ?_,fun X _ _ U x he=> (ht d X U x he).mono (le_max_right ..)⟩
   · unfold bornPair; simp only[tulip_gauge]; exact LinearIsometry.inner_map_map (⟨G.adjoint (a 0), G.norm_adjoint (a 0)⟩:G.Color →ₗᵢ[ℝ] G.Color) _ _
   obtain ⟨D,hD,H⟩:=atp G k 1 zero_le_one; exact (ht D _ (increment v) 0 (H n _ _ (by simp))).analytic
lemma penny (k:ℕ)(d:ℝ)(hd:0≤ d)(G:Gauge): ∃ Y:ℝ,0≤ Y∧∀ (n:Side)(M:Bool) (i j:Axis), Splendor (Toca (G:=G) M i j) (sprout (0:Site n) 4) k Y d:=by
    obtain ⟨Y,hY,H⟩:=born_house k d hd G; let V:= ∑ _:Axis, Y; let E:=V + |(1/4:ℝ)| *(∑ _:Axis, V)
    have hv:0≤ V:=Finset.sum_nonneg (fun i _=>hY); have he:0 ≤ E:= add_nonneg hv (mul_nonneg (abs_nonneg _) (Finset.sum_nonneg (fun i _=>hv)))
    refine ⟨E,he,fun n M i j=>?_⟩; unfold Toca; split
    next h=> split; swap; · exact spark_zero he
             exact ((sparkle _ _ _ (fun a _=> sparkle _ _ _ (fun b _=>H n a a b))).scale (1/4)).up (fun _ h=>h) (le_add_of_nonneg_left hv)
    next h=> split; · exact spark_zero he
             exact (sparkle _ _ _ (fun a _=>H n i j a)).up (fun _ h=>h) (le_add_of_nonneg_right (mul_nonneg (abs_nonneg _) (sum_nonneg (fun i _=>hv))))
lemma plonk(G:Gauge)(S:Stage)(T:Collar G S.order): ∀ᶠ t:ℝ in atTop,∀ (v:ℝ)(n:Side)(R:Rep G n), Age S t v R→ 20*(high t+10)< n.val→∀ M,Club R t (Plint G n M):=by
   let k:= S.order; obtain ⟨D,hD,H⟩:= shimmer G S k le_rfl T; obtain ⟨Y,hY,hZ⟩:= penny k D hD G;obtain ⟨Z,hQ,Q⟩:=cast_shape G S 48 0 T
   let X:=drumA Y; have hx:0 ≤ X:=sum_nonneg fun _ _=> by positivity
   let C:=∑ _:Axis,X; have hC:0 ≤ C:=sum_nonneg (fun _ _=>hx);
   filter_upwards [radiusB_tendsto.eventually_ge_atTop 2,wnt S (Cube.fee T) (Cube.fee_one T) S.order,Q, (mass hY) (1/50) (by norm_num), (mass hx) (1/50) (by norm_num), (mass hC) (1/50) (by norm_num)] with t ht hP hN hX hZ' hG v n R hr hp M
   obtain ⟨_,_,_,_,h₅,hg⟩:=hN 1100 le_rfl (by unfold towerH;omega) v n R hr
   have ht' :8≤ high t:=by unfold high; omega
   have he(x:Peat G n)(i:ℕ)(a:ℝ)(hp':i≤ high t)(hf:a ≤ Zn.wideM t)(hv:Splendor x (sprout 0 i) k a D): Cubc R t x:= (H t v n R hr h₅ (by omega) _ _ (Or.inl (hv.up (sprout_mono _ hp') le_rfl))).plus (hP.1 _ hf) hf
   let U:= Plint G n M
   have hv(i j:Axis): Bounce (U i j):=by intro a; funext p K; change Toca M i j _=Toca M i j _; rw [pace_add,sub_add_cancel]
   have hb(i j:Axis):Turret.Bond (U i j) (U i j) k 4 0 Y 0 D:= by
       refine ⟨hv i j,hv i j,fun x=> (hZ n M i j).trill (?_),fun x=>?_⟩; · exact (sprout_translation (0:Site n) x 4).trans (by rw [zero_add])
       rw[sub_self]; exact sigh_zero le_rfl
   have hu(i j):= (draftA (hb i j) i le_rfl zero_le_one).read 0
   refine ⟨fun i j=> he _ 4 _ (by omega) hX.2 ((hb i j).read _),hv,fun i j=> he _ _ _ ht' hZ'.2 (hu i j),fun i=> he _ 8 C ht' hG.2 ?_⟩
   exact sparkle _ _ _ (fun b _=> hu b i)
end YM.Trace.Margin
