import YM.RG08.Yamen.Pledge

/-! # Post length list for unmarked and the common gate at j. Delay AFTER deciding L, beta
 at EVERY level earlier than incidence includes the price; neighboring Ω also here. !-/
noncomputable section
namespace YM.RG08.Yamen
open Lattice Laurent Pert.Bulk Forms Room Carrel Steam Isles Rows Rate Stair RG Stationary Bloch Rudder RG08.Mount Tack Anchor Spar Sedan Precision Finset Exterior Nacre PowerSeries Finset.Nat Symmetry Prism Quarry Roost Packets Ducat Mason RG08.Supplies
open Filter
open scoped Classical Matrix BigOperators PowerSeries Topology
set_option autoImplicit false
variable (G:Gauge)(P X: MapPrices)(K:KernelChoices)(Z:ChartRatio G)
local notation "H"=>Yamen.atlas G P X K
-- stage constants q finite later in combination; park post derived solely from patch, branch.
structure Posts (j:ℕ)(T:Patch)(x:ℝ):Prop where
 pos : 1 ≤ x
 length: (T.L.val:ℝ)≤x
 head: (Fintype.card (Head T G):ℝ) ≤ x
 collar: ∀ q ≤ j, max 0 (P.Ω q) ≤ x
 arms:∀ q ≤ j, X.Ω q ≤ x
 plant: planSupply G K P j T.L ≤ x
 key : Cell.key G T K ≤ x
 allowance : Cell.allowance G T (planSupply G K P j T.L) ≤ x
 base:∀ q ≤ j, basis G P X K q ≤ x
 brew :∀ q ≤ j, ∀ i ≤ j,∀ r ≤ i,(H q).cash i r ≤ x
 precision: ∀ q ≤ j,∀ i ≤ j,∀ r ≤ i, ((H q).coats i r)⁻¹ ≤ x
 token :∀ q ≤ j,∀ i ≤ j,∀ r ≤ i, |Ducat.coin G r (gleam P j q) ((H q).need i r) ((H j).coats i r)| ≤ x
 -- post all poems (not from arbitrary inputs), widths from exact choices. all i at q stages. park once each stencil n≤e+2. land all Haar etc.
 stamps :∀ q ≤ j,∀ i ≤ j,∀ r ≤ i,∀ n ≤ j+2,poem G r n ((H q).coats i r) ≤ x
 winds :∀ q ≤ j,∀ i ≤ j,∀ r ≤ i,∀ n ≤ j+2,∀ (h:T.Branches K G),|park h n ((H q).need i r)| ≤ x
 season :∀ q ≤ j,∀ i ≤ j,∀ r ≤ i,∀ n ≤ j+2,|Cairn.layer Z ((H q).need i r) n| ≤ x
private lemma arrange {j:ℕ}{p:ℕ→ℝ→Prop}(h:∀ i ≤ j,∀ᶠ t in (atTop:Filter ℝ),p i t):∀ᶠ t in (atTop:Filter ℝ),∀ i ≤ j,p i t:=by
 induction j with
 | zero=>exact (h 0 (by omega)).mono (fun t ht i hi=> Nat.eq_zero_of_le_zero hi ▸ ht)
 | succ j ih=>exact ((ih fun _ hi=>h _ (hi.trans (Nat.le_succ _))).and (h (j+1) le_rfl)).mono (fun t ⟨ht,hj⟩ i hi=> by by_cases he:i=j+1; exact he ▸ hj; exact ht i (by omega))
private theorem exists_posts (j:ℕ)(T:Patch):∃ x,Posts G P X K Z j T x:=by
 have hw (q:ℕ):∀ᶠ t in (atTop:Filter ℝ),∀ i ≤ j,∀ r ≤ i,(H q).cash i r ≤ t ∧ ((H q).coats i r)⁻¹ ≤ t ∧
    |coin G r (gleam P j q) ((H q).need i r) ((H j).coats i r)| ≤ t ∧∀ n ≤ j+2,poem G r n ((H q).coats i r) ≤ t ∧ (∀ h:T.Branches K G,|park h n ((H q).need i r)| ≤ t) ∧ |Cairn.layer Z ((H q).need i r) n| ≤ t:=by
    refine arrange (fun i hi=>arrange (fun r hr=> (eventually_ge_atTop _).and ((eventually_ge_atTop _).and ((eventually_ge_atTop _).and (arrange (fun n hn=>?_))))))
    refine (eventually_ge_atTop _).and (Filter.Eventually.and ?_ (eventually_ge_atTop _))
    by_cases h:T.Branches K G
    · exact (eventually_ge_atTop (|park h n ((H q).need i r)|:ℝ)).mono (fun x hx _=>hx)
    exact Eventually.of_forall fun _ hp=>False.elim (h hp)
 have hp(q:ℕ):∀ᶠ t in (atTop:Filter ℝ),max 0 (P.Ω q) ≤ t ∧ X.Ω q ≤ t ∧ basis G P X K q ≤ t := (eventually_ge_atTop _).and ((eventually_ge_atTop _).and (eventually_ge_atTop _))
 apply Eventually.exists (f:=atTop)
 filter_upwards [eventually_ge_atTop (1:ℝ),eventually_ge_atTop (T.L.val:ℝ), eventually_ge_atTop (Fintype.card (Head T G):ℝ), eventually_ge_atTop (planSupply G K P j T.L),eventually_ge_atTop (Cell.key G T K),eventually_ge_atTop (Cell.allowance G T (planSupply G K P j T.L)),arrange (fun q (hq:q ≤ j)=> (hw q).and (hp q))] with x hx hs hd ht hk hn hQ
 exact ⟨hx,hs,hd,fun a ha=> (hQ _ ha).2.1,fun a ha=> (hQ _ ha).2.2.1,ht,hk,hn,fun a ha=> (hQ _ ha).2.2.2,fun a ha c hc r hr=> ((hQ _ ha).1 _ hc _ hr).1,fun a ha c hc r hr=> ((hQ _ ha).1 _ hc _ hr).2.1,fun a ha c hc r hr=> ((hQ _ ha).1 _ hc _ hr).2.2.1,fun a ha c hc r hr n hn=> (((hQ _ ha).1 _ hc _ hr).2.2.2 _ hn).1,fun a ha c hc r hr n hn=> (((hQ _ ha).1 _ hc _ hr).2.2.2 _ hn).2.1,fun a ha c hc r hr n hn=> (((hQ _ ha).1 _ hc _ hr).2.2.2 _ hn).2.2⟩

def stamp (T:Patch):ℝ:=(exists_posts G P X K Z T.J T).choose
lemma stamped (T:Patch):Posts G P X K Z T.J T (stamp G P X K Z T):=(exists_posts ..).choose_spec
-- beta payment by j stage. X used all. -/
def shade (ℓ:ℕ→ℕ)(n:ℕ):= if h:∃ T:Patch,T.J=n∧(T.L.val)=ℓ n then Real.exp (stamp G P X K Z h.choose) else 1

def Payment (a:Levels G):Prop:=∀ i:ℕ,
 shade G P X a.clock.kernel Z (fun j=>(a.clock.factor j).val) (a.clock.J (i+1)) ≤ a.clock.hatBeta i
variable {G P X K Z}{a:Levels G}
lemma hatch (h:Payment G P X Z a)(i): stamp G P X a.clock.kernel Z (stone a i) ≤ Real.log (a.clock.hatBeta i):=by
 have hf:=h i; unfold shade at hf
 let g := fun j=> (a.clock.factor j).val
 let j:= a.clock.J (i+1);let K:=a.clock.kernel
 have he : ∃ T:Patch,T.J=j ∧ T.L.val=g j:= ⟨stone a i,rfl, congrArg Subtype.val (a.fits.sameFactor i).symm⟩
 rw [dif_pos he,show he.choose=stone a i from ?_] at hf
 · simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos _) hf
 have hm(P Q:Patch)(h:P.J=Q.J)(hP:P.L=Q.L):P=Q:=by cases P;cases Q;simp_all
 apply hm _ _ he.choose_spec.1 (Subtype.ext (he.choose_spec.2.trans (congrArg Subtype.val (a.fits.sameFactor _))))
end YM.RG08.Yamen
