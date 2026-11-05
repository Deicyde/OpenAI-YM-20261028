import YM.FullVolume.Florid.Plume
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Lotus
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Contract Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse
open Coat Matter ProbabilityTheory Poll Pond
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ E Λ μ x κ w C : ℝ} {Ñ:ChartRatio G}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
namespace Leaf
variable (M : Leaf R) (X : Coat T F) (k:Finset ℕ)
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Bid Shield Eider Flux Hues Rotation
open Packets Art Silica Poll Pond
variable {X':Coat T F} {H: Support c} {I : Finset (Tubular f G)} {Z : Support c} {k k' : Finset ℕ} {l : ℕ}
    {u v : Air f G} (p:Molecule S)
variable (H : Cash W x μ L Q o C T R) {v d b C' B A r: ℝ} {j k : ℕ}{χ:Chi}
    (hX:X.x=x) (hv:X.width=o.K) (he:X.χ=χ) (h:(roster p).flags=∅) (hy:Healthy (Pressure.temp x) (H.unionP p) X.V)
variable {E:Type}[NormedAddCommGroup E][NormedSpace ℝ E][FiniteDimensional ℝ E] {V : E→ Config G c} {y:E}
include hX he hv h hy in
lemma arcPage (_hq:Mode V y j v) (_hx: V y=X.V) (ht:∀ q:S.Choices, Glass P ((planted X p).taggedL q) V y j W): ∀ᶠ z in 𝓝 y, M.picture (vary X (V z)) p W o.a Q.table Q.halo=M.grove (vary X (V z)) p W o.a Q.table Q.halo:=by
  let K:=planted X p; let Y q z:=vary (K.taggedL q) (V z); let Z(t:E):= vary X (V t)
  have hf q: ∀ᶠ t in 𝓝 y,Stained.Hue (Y q t):=Stained.eventual_hue (ht q)
    (H.laws.data.localP F (K.taggedL q) hX hv (planted_valid X p)).sails
  filter_upwards [eventually_all.mpr hf] with y hh
  let L (z:Coat T F):= M.grove z p W o.a Q.table Q.halo
  have hF z: L ((Z y).rinse z)=L (Z y):=by
    unfold L grove; rw [show ((Z y).rinse z).B=X.B from rfl,show (Z y).B=X.B from rfl,show X.B=radiusB x from congr_arg radiusB hX]
    split
    next hQ =>
      apply congr_arg likely; funext q; let I:=podium S G (H.unionP p) (radiusB x); let b X:= M.cinema (F:=F) (T:=T) X p W o.a Q.table Q.halo I
      have hpz : b ((preps (vary X (gauge z (V y))) (roster p)).taggedL q)=b ((Y q y).rinse z) := (M.casin X p H hX h hy q _ _ (show Agrees _ (gauge z (V y)) (gauge z (V y)) from fun i _ _=> rfl)).symm
      have hpc : b (Y q y)= b ((preps (vary X (V y)) (roster p)).taggedL q):= M.casin X p H hX h hy q _ _ (show Agrees _ (V y) (V y) from fun i _ _=> rfl)
      change b _=b _; refine hpz.trans ((?_ : b ((Y q y).rinse z)=b (Y q y)).trans hpc); have ht:=H.laws.data; unfold b I; rw [← chargedU];
      apply M.coastal (Y q y) p (show Intake P T (Y q y).x R from hX.symm ▸ H.laws.intake) (show ShellAccess S G (Y q y).x W (Y q y).width o.γ from (by change ShellAccess S G X.x W X.width o.γ; rw [hX,hv]; exact H.laws.data.access)) _ z Q.table_exists _ _ (hh q)
      · apply mul_pos o.large; unfold Coat.t; change 0<Pressure.fiery G X.x _; rw [hX]; exact H.laws.data.room.fiery
      unfold Coat.t; change 4*_ *Pressure.fiery G X.x _ < _; rw [hX,ht.funds.length_eq]; exact H.laws.data.covers
    next => rfl
  change (∫ z,L ((Z y).rinse z) ∂_)=L _; simp_rw [hF]; simp; rfl
end Leaf
end YM.PhysicalNext.Repeat.Lotus
