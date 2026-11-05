import YM.FullVolume.E6.Bourse
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
structure Bids (M:Bank) (Q:ConnectedActivityE6.Target G P)(o:Target.Order G W)(χ:Chi)(j:ℕ)(x:ℝ)(K:ℕ→ Epoch Λ)(n:ℕ)(i:Head S)(v:ℝ): Prop where
    force:∀ (F:Forest S.ratio) (X:Coat (K n).tubes F), X.x=x → X.width=o.K → X.χ=χ → X.manifest → ∀ l z, |X.vertex (K n).kin Q.table W o.a l Q.halo z i| ≤ v
    regular:∀ (F:Forest S.ratio) (X:Coat (K n).tubes F), X.x=x → X.width=o.K → X.χ=χ → X.manifest → ∀ l (z:Air f G), Healthy (Pressure.temp x) (areas (K n).kin (K n).tubes Q.halo (radiusB x) i) X.V →∀ (E:Type)[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E](V:E→ Config G c)(p:E), V p=X.V → Mode V p j M.v →
        let u:=worldZ X (K n).beta z
        Brush j v 1 (fun y=> Polar.ember (vary X (V y)) o.a (K n).kin W Q.table (steer X M.A u (V y)) (X.input u) (course X M.A (K n).beta z (V y)) l Q.halo i) p
variable (M:Bank)(I:Depot Q o x μ L C₀ K) {χ: Chi}(Y:∀ n,Station M χ (I n) j)(h:Sweep K)
set_option quotPrecheck false
local notation "Hn" => Bids M Q o χ j x K
local notation "b"=> radiusB x
local notation "core"=> (K 0).kin
local notation "a'"=> o.a
include I Y
open Epoch
lemma gifts : ∃ v:ℕ→LogIndex c f→ℝ,Sparse v ∧ ∀ n i, Loose i→ Hn n (.inr (.inr (.inl i))) (v n i):=by
   let r:=M.P0; let K'(n:ℕ):=(Y n).fleets.M.stencil
   have h' : 0≤r:= zero_le_one.trans (K' 0).active
   let u(n:ℕ):=(K' n).flair; let w(n:ℕ):=ConnectedActivityE6.rates (I n).v (I n).w ((I n).alarms*Coat.topStorm S.patch)
   let Ψ(n:ℕ)(i: LogIndex c f):= if Loose i then u n (opt c f i)*(1+r*spanW (K 0).tubes core b Q.halo (.inr (opt c f i)))^j else 0
   have hx : Sparse Ψ:= (K 0).sparseR (u:=u) (fun n=> (K' n).uses) r h' j
   let g(n:ℕ)(i: LogIndex c f):= if Loose i then w n (opt c f i) else 0
   have hv : Sparse g:=by simpa only [pow_zero,mul_one] using (K 0).sparseR (u:=w) (fun n=> (I n).fares) r h' 0
   refine ⟨_,hx.tug hv,fun n i hL=>?_⟩
   let p:=opt c f i
   constructor
   · intro F X hX hK hχ hM _ q; let U:=(I n).quotes F X hX hK hM
     refine (U.2.1 i q).2.trans ?_
     rw [show (I n).w i=g n i from (if_pos hL).symm]; exact le_add_of_nonneg_left (hx.value ..)
   intro F X hX hK hχ hM l z hZ E _ _ _ V p' H' H u'; have hz:= K' n |>.stream E F X V _ _ _ z hX hK hχ hM H (((Y n).fleets.M.rays F X hX hK hχ hM E V p' H' H).2 z|>.1) l (Sum.inr p) (show Healthy _ _ _ from (by rw [hX]; exact hZ))
   apply hz.trim.climb _ le_rfl; rw [show X.B=b from congr_arg _ hX]; have hl : Ψ n i=u n (opt c f i)*(1+r*spanW (K 0).tubes core b Q.halo (.inr p))^j:= if_pos hL
   refine le_trans (le_of_eq hl.symm) (le_add_of_nonneg_right (hv.value ..))
lemma dross : ∃ v:ℕ→ WarningAt c f→ℝ,Sparse v∧ ∀ n i, Hn n (.inr (.inr (.inr i))) (v n i):=by
   let A:= topStorm S.patch; let V(i: WarningAt c f):= (A+1)*(1+M.U*(1+coverNumber b (field_support S b Q.halo i)))^j
   obtain ⟨p,hp⟩:= (Set.finite_range V).bddAbove; have ha:0 ≤ A:= zero_le_one.trans (topStorm_one _)
   refine ⟨fun _ _=> A+|p|,Sparse.rings (I:=Finset.univ) _ (fun _ i hi=> (hi (mem_univ _)).elim) (add_nonneg ha (abs_nonneg p)) (fun _ _=>add_nonneg ha (abs_nonneg _)) (fun _ _ _=> le_rfl),fun n i=>?_⟩
   constructor; · intro F X hX hK hχ hM k z; exact (X.fires_at _ _ _ _ k i).trans (le_add_of_nonneg_right (abs_nonneg _))
   intro F X hX hK hχ hM l z H E _ _ _ U p' hv hS u'
   apply (((Y n).fleets.curtain F X hX hK hχ hM E U p' hv hS z).2 i l).trim.climb _ le_rfl; rw [show X.B=b from congr_arg _ hX]; exact ((hp (mem_range_self (f:=V) i)).trans (le_abs_self _)).trans (le_add_of_nonneg_left ha)
lemma merchant : ∃ v:ℕ→ Stores S→ℝ,Sparse v∧∀ n i,Hn n (.inl i) (v n i):=by
   choose f hf ht using fun A:Stores S=> tariffC I A C₀; choose g hg hL using fun A:Stores S=> tariffC I A M.c
   let u(A):=g A*(1+M.P0*1)^j+f A; have ht' : 1≤ M.P0:= (Y 0).fleets.M.stencil.active; have hr A:0≤u A:=add_nonneg (mul_nonneg (hg A) (pow_nonneg (by linarith) _)) (hf A)
   obtain ⟨C₀,hC⟩:= (Set.finite_range u).bddAbove
   refine ⟨fun _ i=>u i,Sparse.rings (I:=Finset.univ) |C₀| (fun _ i hi=> (hi (mem_univ _)).elim) (abs_nonneg _) (fun i A=>hr A) (fun i A _=> (hC (mem_range_self A)).trans (le_abs_self _)),fun n i=>?_⟩
   constructor
   · intro F X hX hK hχ hM l z; unfold vertex; simp only [Sum.elim]; split
     · refine ((I n).quotes F X hX hK hM|>.2.2.1 ..).trans ((ht i n).trans ?_); exact le_add_of_nonneg_left (mul_nonneg (hg i) (pow_nonneg (by linarith) _))
     rw [abs_zero]; exact hr i
   intro F X hX hK hχ hM l z hZ E _ _ _ V p' H' H u'; let P':=(Y n).fleets; let Ξ:=P'.M.stencil
   have hz:= Ξ.stream E F X V _ _ _ z hX hK hχ hM H ((P'.M.rays F X hX hK hχ hM E V p' H' H).2 z|>.1) l (.inl i) (show Healthy _ _ _ from ?_); swap; · rw [hX]; exact hZ
   apply hz.trim.climb _ le_rfl; unfold stout Mixed.costs; simp only [Sum.elim]; split
   · exact (mul_le_mul_of_nonneg_right (hL i n) (show 0≤(1+M.P0*1)^j from pow_nonneg (by linarith) _)).trans (le_add_of_nonneg_right (hf _))
   rw [zero_mul]; exact hr i
end YM.ConnectedActivityE6.Lim
