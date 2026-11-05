import YM.FullVolume.E6.SheetP
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
open Poll
variable {ι:Type}[Fintype ι][DecidableEq ι]
private lemma pennon {η r:ℝ}{A: Matrix ι ι ℝ}{a:ι→Site c}{m:ℕ}{B:ℝ}(h:Allow A a m η r B)(u:Body ι):
     lens₀ A u ≤ (((Real.sqrt (2*Real.pi))^Fintype.card ι)⁻¹ * Real.exp (-Real.log A.det/2)) * Real.exp ((-(B⁻¹/2))*‖u‖^2):=by
   let v:= u.ofLp; have hp:=lower_inverse h.relented h.weather.1.le h.fuel h.symmetry h.ground h.down.le h.initial.1 v
   have hx: dotProduct v v=‖u‖^2:=by simp_rw [dotProduct, EuclideanSpace.real_norm_sq_eq,pow_two]; rfl
   rw [hx] at hp
   unfold lens₀; rw [mul_assoc,←Real.exp_add]; apply mul_le_mul_of_nonneg_left (Real.exp_monotone _) (by positivity); unfold v at hp; change B⁻¹*_ ≤ _ at hp; nlinarith only [hp]
private lemma remits {a:ι→Site c}{η r:ℝ}{B:ℝ}{m:ℕ}{A:ℕ→Matrix ι ι ℝ}(h:∀ n,Allow (A n) a m η r B): BddAbove (Set.range fun i=> -Real.log (A i).det):=by
    by_contra hh; obtain ⟨f,hf⟩ : ∃ f:ℕ→ℕ,∀ n:ℕ, (n:ℝ) < -Real.log (A (f n)).det:= by
         have ht(n:ℕ):= not_bddAbove_iff.mp hh (n:ℝ); choose b hb hB using ht; choose i hi using hb; exact ⟨i,fun i=> (hB i).trans_eq (hi i).symm⟩
    let U:= (Ultrafilter.of (atTop:Filter ℕ)); have hX : (↑U:Filter ℕ) ≤ atTop:= Ultrafilter.of_le _
    have hp:Glints U (fun i=>A (f i)) (fun i=>A (f i)):=Glints.fibers fun p=> Glints.fibers fun q=> FullVolume.Shadow.flowers (x:=0) (b:=B) (Eventually.of_forall fun i=> by simpa using only_price (h (f i)).price (h (f i)).eta.le p q)
    obtain ⟨R,hR,-⟩:=hp
    have hg:= Buds.assured (K:=R) (Eventually.of_forall fun i=> h (f i)) hR
    have hg' : Tendsto (fun i=> -Real.log (A (f i)).det) (U:Filter ℕ) (𝓝 (-Real.log R.det)):=by
         exact (((show Continuous (fun K:Matrix ι ι ℝ=> K.det) by fun_prop).continuousAt.tendsto.comp hR).log hg.det_pos.ne').neg
    obtain ⟨i,hi,h⟩:= ((hg'.eventually (gt_mem_nhds (lt_add_one _))).and (hX (show ∀ᶠ n:ℕ in atTop, -Real.log R.det+1<n from tendsto_natCast_atTop_atTop.eventually_gt_atTop _))).exists; exact ((hf i).trans_le hi.le|>.not_gt h)
lemma oasis {η r B:ℝ}{a:ι→Site c}{m:ℕ}{A:ℕ→Matrix ι ι ℝ}(h:∀ n,Allow (A n) a m η r B): ∃ b C:ℝ, 0<b∧0<C∧ ∀ n (u:Body ι),lens₀ (A n) u≤ C * Real.exp (-b*‖u‖^2):=by
    obtain ⟨D,hD⟩:=remits h; refine ⟨B⁻¹/2, (((Real.sqrt (2*Real.pi))^Fintype.card ι)⁻¹ * Real.exp (D/2)), half_pos (inv_pos.mpr (h 0).fuel), by positivity,fun n u=>?_⟩
    refine (pennon (h n) u).trans ?_; gcongr; exact hD ⟨n,rfl⟩
lemma crystal {b:ℝ}(he:0<b)(m:ℕ) : Integrable (fun z:Body ι=> Real.exp (-b*‖z‖^2)*(1+‖z‖)^m):=by
    let y:=b/2; have hh:0<y:=half_pos he; have hp := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (b:=(y:ℂ)) (by exact hh) 0 (0:Body ι)).norm
    have hg: Integrable (fun z:Body ι=> Real.exp (-y*‖z‖^2)):=hp.congr (ae_of_all _ (fun z=> by dsimp only; rw [Complex.norm_exp]; simp [← Complex.ofReal_pow]))
    let C := (m:ℝ)^2/(4*y); refine ((hg.const_mul (Real.exp C)).mono' (by fun_prop) (ae_of_all _ fun z=>?_)); rw [Real.norm_of_nonneg (by positivity : 0 ≤ Real.exp _*(1+‖z‖)^m)];
    have ht := Real.add_one_le_exp ‖z‖; rw [add_comm] at ht
    apply (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) ht m) (Real.exp_pos (-b*‖z‖^2)).le).trans
    rw [←Real.exp_nat_mul,← Real.exp_add, ← Real.exp_add]; apply Real.exp_monotone; unfold C
    rw [show b=2*y from by unfold y; ring]; field_simp; nlinarith [sq_nonneg ((m:ℝ)-2*y*‖z‖)]
end YM.ConnectedActivityE6.Lim
