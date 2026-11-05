import YM.RG08.Crown.Pupil

/-!
# Full Fk Wilson input represented via local curvature chords, all finite horizons independently
 of L. (Uses actual Wilson. Lean versions of Guns etc charge factors direct p separately; don't
 substitute this as Phys path). -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Crown
open Carrel Camera Room Cloud Glyph Function Finset MvPolynomial Filter Lattice Rudder Forms Pert.Bulk
open Wilson WilsonStartup Design Exterior Anchor Rudder.Symmetry RG
open scoped ContDiff Topology PowerSeries BigOperators Classical RealInnerProductSpace Matrix.Norms.Frobenius
variable {G:YM.Gauge}{P:Side}{k:ℕ}

lemma march (p:Site P)(j:PlaqAxes)(K k:ℕ)(h:k≤K):
 tap k (flask (fun x:Cellar (Bedge G P)=>G.price (faceValue (offers G x) (p,j))))=∑ i∈range (K+1), if i=0∨ Odd i then 0 else tap k (flask (sheet G p j i)):=by
 rw [wardFace];change tap k (spool (lug _) _)=_;rw [ships]
 let s:=lug (rescaleFields (curvatureCells (G:=G) p j))
 -- contextual valuation valuation
 apply Eq.trans (Finset.sum_congr rfl fun i (hi:i∈_)=>?_)
 · apply Finset.sum_subset (s₁:= range (k+1)) (Finset.range_mono (by omega)) (fun i _ hi=>?_)
   split; · rfl
   rw [article,tap,PowerSeries.coeff_X_pow_mul',if_neg (by simp only [mem_range] at *;omega)]
 by_cases he:i=0∨Odd i
 · rcases he with rfl|ht
   · simp_rw [nil,map_zero];simp
   rw [if_pos (Or.inr ht),absent G _ ht,map_zero];exact map_zero _
 rw [if_neg he,article,tap,tap,tap,PowerSeries.coeff_X_pow_mul',if_pos (by simpa using hi),belt_c,←orient_photo]
 -- bypass

lemma power (G:YM.Gauge)(p:Site P)(j:PlaqAxes): Pace (fun x:Cellar (Bedge G P)=>G.price (faceValue (offers G x) (p,j))):=by
 apply Work.F03.price_smooth
 obtain ⟨C,hC,H⟩:=work G 0
 exact (Push.Uniform.travel_jets (U:=offers G) (H P) p (w:=Lattice.square ..) (Nat.le_refl _)).analytic

def opening (G:YM.Gauge) (k:ℕ)(x:Coord (n:=k))(i:Tape k G.ColorIndex):ℝ:=if ∃ b:TypeFace 2,x=fun (_:Fin k)=>(0,b) then pixel G k i else 0
def sheetCard (G:YM.Gauge)(k:ℕ):Flake k (Market (Rayk G 2)):=fun x=> opening G k (fun i=>((x i).1,(x i).2.1)) (fun i=>(x i).2.2)
def prize (G:YM.Gauge)(k:ℕ):Rudder.Raw G.ColorIndex k:=Anchor.extend 2 (grown (sheetCard G k))

-- When converting to deposit all surviving atom indices represent actual rooted plaquettes
lemma terminal_charge (G:YM.Gauge)(k:ℕ)(o:Fin k)(b: Coord (n:=k))(i:Tape k G.ColorIndex):
    (deposit (Anchor.compress 2 (prize G k)) o b).coeff i=opening G k b i:=by
 rw [show Anchor.compress 2 (prize G k) = grown (sheetCard G k) from funext (fun x=>extend_top ..)];change neck _ _ _=_
 by_cases hh : (b o).1=(0:Cover)
 · rw [neck,if_pos (show (Carrel.join b i o).1=0 from hh),grown,tsum_eq_single (0:Cover) (by
      intro x hx
      unfold sheetCard opening;rw [if_neg (by
        rintro ⟨v,hv⟩; have he:=congrArg (fun y=> (y o).1) hv
        change (b o).1+-x=(0:Cover) at he;rw [hh,zero_add,neg_eq_zero] at he;exact hx he) ])];simp only [neg_zero,sway_zero];rfl
 rw [neck,if_neg (show (Carrel.join b i o).1≠0 from hh),opening,if_neg (by rintro ⟨v,rfl⟩;exact hh rfl)]

lemma earned {σ:ℝ}(G:YM.Gauge)(k:ℕ)(_o:Fin k):∃ D:ℝ, 1≤D∧ Held (carpet (Tone G.ColorIndex)) σ D (prize G k):=by
 -- finite sum via finite reach of card, set size; prove ENN.Cost.ne_top
 let X:=Cost (sheetCard G k) σ
 let f(i:TypeFace 2)(j:Tape k G.ColorIndex):Slide (Rayk G 2) k:=fun t:Fin k=>(0,i,j t)
 let S:Set (Slide (Rayk G 2) k):= Set.range (Function.uncurry f)
 have he:S.Finite:=Set.finite_range _
 have hz(x:Slide (Rayk G 2) k)(hx:x∉S):sheetCard G k x=0:=by
   unfold sheetCard opening;split; next h=>
      exfalso;apply hx;obtain ⟨v,hv⟩:=h
      use (v,fun i=>(x i).2.2);funext i;have T:=congrFun hv i; change (0,v,(x i).2.2)=_;apply Prod.ext; rotate_left; apply Prod.ext;rotate_left;rfl; rotate_left
      · exact congrArg (fun t:Cover×TypeFace 2=>t.2) T.symm
      exact congrArg (fun t:Cover×TypeFace 2=>t.1) T.symm
   rfl
 have hh:X≠⊤:=by
   unfold X Cost;rw [tsum_eq_sum (s:=he.toFinset) (by intro x hx; rw [hz x (by simpa using hx)];simp [bill])];apply ENNReal.sum_ne_top.mpr; intro i _; exact ENNReal.ofReal_ne_top
 have hp:1 ≤ max X.toReal 1:=le_max_right ..
 refine ⟨_,hp,Anchor.expand_cost (grown_held ⟨(by linarith),?_⟩)⟩
 change X≤_
 conv_lhs=> rw [←ENNReal.ofReal_toReal hh]
 gcongr; exact le_max_left ..
end YM.RG08.Crown
