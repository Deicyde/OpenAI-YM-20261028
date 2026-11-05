import YM.FullVolume.Poesy.Lyric
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
variable {ι κ:Type}{A:ι→ RegularAddress c}{F H:ℕ→ ι→ Config G c→ℝ}{D:BudgetPoint}{σ r:ℝ}
namespace Cad
open Geo WilsonStartup Seat
set_option quotPrecheck false
variable {d:ℕ}[NeZero d]
-- shape common legs.Seat.Establish estimates via Wages price polynomial and growth.
abbrev team (D:ℕ→Ink G (d+1) →ℝ) (i:ℕ): Atom G (d+1):= ⟨letter i,D i⟩
variable {A B':ℕ→ℕ→Ink G (d+1) →ℝ}{c:Side}{p:BudgetPoint}
lemma tint (he:∀ i,SumBudget (fun j=> (team (A i) j).budget σ) r)(h:0<σ)(hw:∀ i j,(team (A i) j).Invariant): PulseWise p (pitch (n:=c) (team (A 0))) (fun n=> tuneAtom (team (A n)) 1):=by
    have hx : Sparse (fun i=> Song.sine p (team (A i)) 1):=by
        refine neptune (r:=tenor G (d+1) p σ r 1) (Shade.stretch d) ?_ (fun n i=>sine_pos ..) (half_pos h) fun i=>?_
        · intro k; let x:ℕ→ℝ:= chants d (-1)
          have hp:∀ᶠ i in cofinite,x i<Real.exp (-(k:ℝ)):= (silts d zero_lt_one).tendsto_cofinite_zero.eventually (gt_mem_nhds (Real.exp_pos _)); rw [Nat.cofinite_eq_atTop] at hp; obtain ⟨D,hD⟩:=eventually_atTop.mp hp; refine ⟨Finset.range D,fun i hi=> Finset.mem_range.mpr (lt_of_not_ge fun hz=>?_ )⟩
          have hy:=hD _ hz; refine LT.lt.false (lt_of_le_of_lt (Real.exp_monotone ?_) hy)
          unfold x at hy; change -_≤ (-1:ℝ) * ↑(Shade.stretch d i); simp only [neg_one_mul]; exact neg_le_neg (Nat.cast_le.mpr hi)
        have hP:=Song.act_lp p (team (A i)) 1 h (he i); simp_rw [show ∀ j,(team (A i) j).length=_ from fun j=>pervade (team (A i)) (fun _=>rfl) j] at hP; exact hP
    refine ⟨fun i j=> (pitch_charge p (team (A i)) j 1 (hw i)).1,⟨_,sparking hx,fun i j=> (pitch_charge p (team (A i)) j 1 (hw i)).2⟩⟩
lemma herd (h1:∀ i,SumBudget (fun j=> (team (A i) j).budget σ) r)(h2:∀ i,SumBudget (fun j=> (team (B' i) j).budget σ) r)(h:0<σ)(hw:∀ i j,(team (A i) j).Invariant)(hp:∀ i j,(team (B' i) j).Invariant)(he:∀ i k,Glints atTop (fun n=>A n i k) (fun n=> B' n i k)): Canopy p (pitch (n:=c) (team (A 0))) (fun n=> tuneAtom (team (A n)) 1) (fun n=> tuneAtom (team (B' n)) 1):=by
    let D(i:ℕ):= A i-B' i; have hd n i v: (team (D n) i).poly v=(team (A n) i).poly v-(team (B' n) i).poly v:=by unfold Atom.poly team; simp only [D,Pi.sub_apply,sub_mul,sum_sub_distrib]
    have hg i k:(team (D i) k).Invariant:=by
         intro u x; rw [hd,hd,hw i k u x,hp i k u x]
    refine ⟨tint h1 h hw,tint h2 h hp,fun ⟨s,i⟩ v hv=>?_⟩; have hz:Tendsto (fun n=> (team (D n) i).magnitude) atTop (𝓝 0):=by
         unfold Atom.magnitude; have hQ:=tendsto_finsetSum (ι:= Ink G (d+1)) Finset.univ fun k _=> (he i k).shrank.abs; simpa only [team,D,Pi.sub_apply,abs_zero,sum_const_zero] using hQ
    have hV : Tendsto (fun n=> Song.sine p (team (D n)) 1 i) atTop (𝓝 0):=by
         let f(n:ℕ):=team (D n) i; have hf : ∀ n,(f n).length= (f 0).length:=fun _=>rfl
         simp_rw [Song.sine, Wages.scan, show ∀ n,(team (D n) i|>.length)=_ from hf]; convert! ((((tendsto_const_nhds.mul hz).mul_const _).const_mul _).const_mul _) using 1; simp
    filter_upwards [hV.eventually (ge_mem_nhds hv)] with n hn
    have he' : tuneAtom (team (A n)) 1 (s,i)- tuneAtom (team (B' n)) 1 (s,i)=(tuneAtom (team (D n)) 1 (s,i)):= by
           ext U; unfold tuneAtom; simp only [Pi.smul_apply,Pi.sub_apply, Atom.unmasked]; rw [hd]; exact (smul_sub ..).symm -- smul_sub
    change p.supBounds _ _ (_-_) _; rw [he']; exact CouplingShape.sup_larger (pitch_charge p (team (D n)) (s,i) 1 (hg n)|>.2) hn
end Cad
end YM.ConnectedActivityE6.Lim
