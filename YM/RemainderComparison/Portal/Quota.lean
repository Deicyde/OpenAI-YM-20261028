import YM.RemainderComparison.Portal.Cantor
import YM.RemainderComparison.Auxiliary.Day
set_option autoImplicit false
noncomputable section
namespace YM.RemainderComparison.Portal
open Function Filter Lattice RG RG.Patch Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior ConnectedActivityE6 Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Mask Work.F03 Presented LabelSum Sector Footprint Packets SliceRows Control Window Pulse PhysicalNext.Repeat Gas
open Coat Matter ProbabilityTheory Poll Pond Census Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill Shield Eider Flux Art Silica Poll Pond Lotus
open Itinerary Animals March Captain Stained Ursell Trees Reserves
open Merge Palette Next.Scheduling Raw Itinerary Opacity Cascade Lyric Daisy Halo Height
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {ι : Type} [Fintype ι]
variable {G : Gauge} {c f L : Side} {S : StepData c f} {P:Teller G} {T: Tube G S} {F : Tree.Forest S.ratio} {R : Rep G f}
    {p : Molecule S} {m : ℕ} {W a r σ μ x κ C : ℝ}
    {Q: YM.ConnectedActivityE6.Target G P} {o: ConnectedActivityE6.Target.Order G W}
variable (M:ι→Lotus.Leaf R)(H:Cash W x μ L Q o C T R) {q A B b e u v d L' Gp:ℝ}{j n k s J:ℕ}(χ:Chi)
variable (N: Captain H j q d v u A b r B e n χ) (Ξ:Utopia H j v d r q χ)
variable (l:ι→ℝ) {T' S' δ B' b' τ ε:ℝ}
local notation "V'" => Q.costs L μ R.beta x q
local notation "LT" => Mixed.lengths S V' (ConnectedActivityE6.lengths T R)
local notation "Z" => radiusB x





open Marker Next.Rank.Glyph Next.Rank.Exponential Sleet
local notation "Yv" => veil ι
local notation "cardboard" => Stock.census ι
open Aux

-- pointwise assembler. Requires exact same representation of all marked inputs.
-- Distinguish denominator control inside Council (no assumptions about vacuum mass).

lemma valves (A B: Cabinet ι)(d:ℝ)(hd:0<d)(h:deckR A=(d:ℂ) • GridRenewal.Rain.cyclone (deckR B)):
   A (quiet ι)=d*Real.exp (B (quiet ι)) ∧
     ∀ i,i≠quiet ι → sWard (fun j=>A j/A (quiet ι)) i=B i:=by
  let x:=A (quiet ι); let y:=B (quiet ι); let Y':=GridRenewal.Rain.fresh (deckR B); let X i:=A i/x
  have hp:Y'.part (quiet ι)=0:=GridRenewal.Rain.unwritten _
  rw [GridRenewal.Rain.power,Poly.product_bead,smul_smul] at h
  have hh : deckR A=((d*Real.exp y:ℝ):ℂ) • Poly.pass Y':= by simp only [Complex.ofReal_mul, Complex.ofReal_exp]; exact h
  have hx' : x=d * Real.exp y:=Complex.ofReal_injective (show _ from (by change (deckR A).part _= _; rw [hh,Poly.part_smul,Poly.pass_part Y' hp,mul_one]))
  have hx:0<x:= hx' ▸ mul_pos hd (Real.exp_pos _)
  refine ⟨hx',fun i hi=>?_⟩
  have hF : deckR X=(↑(x⁻¹):ℂ) • deckR A:=by
    ext i; change (↑(A i/x):ℂ)= (↑(x⁻¹):ℂ)*(A i:ℂ); simp [div_eq_mul_inv,mul_comm]
  have hg: Expands Y' (deckR X):=by refine ⟨hp,?_⟩; rw [hF,hh,← hx', Complex.ofReal_inv,smul_smul,inv_mul_cancel₀ (by exact_mod_cast hx.ne'),one_smul]
  have hX:= Poly.pass_part Y' hg.1; rw [hg.2] at hX
  have ht: deckR (sWard X)=Y':=(sprints X _).trans ((rolls _ hX).uniq hg)
  apply Complex.ofReal_injective; change (deckR (sWard X)).part i = (deckR B).part i
  rw [ht, show Y'.part i=_ from Next.Rank.Exponential.part_sub .., show (GridRenewal.Rain.bead _ _).part i=0 from ?_,sub_zero]
  exact (Poly.part_send (quiet ι) i _).trans (if_neg hi)
section
variable (V:BudgetPoint) (hx:V.threshold=Pressure.temp x) (F:Tree.Forest S.ratio)
    (hf:V.B=radiusB x) (hs:V.supportExponent≤a)
variable {P':Type}[Fintype P'] {X:P'→Site f} {p':ι→ Finset P'} (h:Premium Q L x a μ b' B j n k s J m Gp)(hl:Scale X p' M l m σ Gp S)(hh: Heroes H N.conduit A B n) (hH:Heavy N.conduit)(hr:radiusCost Q L σ)
local notation "O'" U:max => overhead (Greenbelt.prism T x χ o.K U F) R Q.table
local notation "ⵐ" => (Portal.shelf M H χ l)
include hx hf hs h hl hh hH hr
lemma tillers (U:Config G c)(ht:flags V.threshold U=∅) :
     pushed (S:=S) M l U (quiet ι)= O' U *Real.exp (ⵐ U (quiet ι)) ∧
      ∀ i,i≠quiet ι → sWard (fun j=> pushed (S:=S) M l U j / pushed (S:=S) M l U (quiet ι)) i= ⵐ U i:=by
   obtain ⟨-,hs'⟩:=Portal.sunny M H χ N l V hx F hf hs h hl hh hH hr U ht
   rw [parcel M H] at hs'
   exact valves _ _ _ (overhead_pos (Greenbelt.prism T x χ o.K U F) H) hs'
end
-- align mere representation vs auxiliary H fields.
variable (E:modes ι→ Config G f→ℝ)
structure Parade (M:ι→ Leaf R)(T:Tube G S)(B : BudgetPoint) (l:ι→ℝ)(E:modes ι→ Config G f→ℝ):Prop where
   atExhaust p : palette (S:=S) M l p=inputC T B R.beta (E p)

variable (B':BudgetPoint)(V:BudgetPoint){F:Tree.Forest S.ratio} (k':S.Choices)(ρ: Bid.Dir G c → AxisChart G F)
variable (hκ : Parade M T B' l E)
open Sienna Fare Lapis
local notation "Ek" => E (quiet ι)
local notation "μp" U:max => (pushed (S:=S) M l U)
local notation "O'" U:max => overhead (Greenbelt.prism T x χ o.K U F) R Q.table
local notation "ⵖ" => (Portal.shelf M H χ l)
include hκ
lemma hinges (U:Config G c)(p:modes ι) : (μp U) p=Aux.powder T B' R.beta U (E p):=by rw [pushed,hκ.atExhaust]; rfl
variable {hf:V.B=radiusB x} (hs:V.supportExponent≤a){P':Type}[Fintype P'] {X:P'→Site f} {p':ι→ Finset P'} (h:Premium Q L x a μ b' B j n k s J m Gp)(hl:Scale X p' M l m σ Gp S)(hh: Heroes H N.conduit A B n) (hH:Heavy N.conduit)(hr:radiusCost Q L σ)(hx:V.threshold=Pressure.temp x)
include V hx hf hs h hl hh hH hr
def baser (T:Tube G S) (R:Rep G f)(V:BudgetPoint) (y:Config G c) := R.beta*averaged (fun t=>∑ i:Pressure.Cell c, T.down.baseTerm T.low V (pull t 0 y) i)
lemma junction (U:Config G c)(ht:flags V.threshold U=∅):
     let y i:= Aux.powder T B' R.beta U (E i); let u:= y (quiet ι)
     0<u ∧ Real.log u=Song.weighty H χ F * Fintype.card (Site c) - baser (T:=T) (R:=R) V U + Portal.shelf M H χ l U (quiet ι) ∧
       ∀ i,i≠quiet ι → sWard (fun j=>u⁻¹*y j) i= Portal.shelf M H χ l U i:=by
   intro y u
   have he U i: (μp U) i= Aux.powder T B' _ U (E i):= hinges M l E B' hκ U i
   obtain ⟨hA,hC⟩:= tillers M H χ N l V hx F hf hs h hl hh hH hr U ht
   have hx' :0< O' U:= overhead_pos (Greenbelt.prism T x χ o.K U F) H
   have hp : (μp U) (quiet ι)=u:=he ..
   refine ⟨(hp.symm.trans hA).symm ▸ mul_pos hx' (Real.exp_pos _),?_,fun i hi=>?_⟩
   · rw [← hp,hA,Real.log_mul hx'.ne' (Real.exp_pos _).ne', Song.grants (χ:=χ) (p:=V) (J:=H) (O:=F) hx,Real.log_exp,Real.log_exp] -- inspect params
     rfl
   rw [← hC i hi]; refine congr_arg₂ (fun a:Cabinet ι=> fun i=>sWard a i) (funext fun j=>?_) rfl
   rw [hp,he, div_eq_mul_inv]; unfold y; ring
end YM.RemainderComparison.Portal
