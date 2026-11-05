import YM.RG08.Crossing.Courage
/-! # Less events by (grade, reversed rank) and same transfer through probe -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Wings
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open scoped BigOperators Topology Real Classical
variable {X : Chain} {G : Gauge} {K : KPrices X.kernel} {g : KGate K} {P : Lending G X.kernel} {E : ℕ} {S : Prism G X.kernel g P E} {ν : G.ColorIndex} {D : ChartRatio G}
variable {I : Type} {u : I→Windows} {r s e q : ℕ} {δ : Wings u 1→ℝ}
-- convenience: forecasts absolute vs twin by A(t), apply common probe.
abbrev moon (X : Chain) (ν : G.ColorIndex) (D : ChartRatio G) (t : Wings u s) := X.album ν D t.N t.i
abbrev orbit (X : Chain) (t : Wings u s) := Chain.column G X t.N t.i -- G explicit? include
abbrev lunar (X : Chain) (ν : G.ColorIndex) (D : ChartRatio G) (t : Wings u 1) := X.compassRaw ν D t.N t.i
abbrev dark (X : Chain) (ν : G.ColorIndex) (D : ChartRatio G) (e r) (t : Wings u 1) :=
   scramble ν (X.patch t.i) D X.kernel (Chain.curve G X t.N t.i) (Chain.predict G X t.N t.i) (moon X ν D t.up) e r

lemma rallies (h : X.Wake G)(hv : LocalRatio D)(t : Wings u 0) : RunsInk ν (orbit X t) (moon X ν D t) :=
    { totes:=X.packing ν D h hv t.cut,tune:= (Chain.high_stocks X ν t.N t.i).1,glows:=(Chain.high_stocks X ν t.N t.i).2.1,prose:=(Chain.high_stocks X ν t.N t.i).2.2}
lemma ralliedK {b : ℕ} (h : X.Wake G)(hv : LocalRatio D) : RunsInk ν (Chain.column G X b b) (wilsonTop ν) := by
  rw [← X.album_top ν D b]; exact {totes:=X.packing ν D h hv (le_refl b),tune:=(X.high_stocks ν b b).1,glows:=(X.high_stocks ν b b).2.1,prose:=(X.high_stocks ν b b).2.2}

lemma obverse (h : X.Wake G)(hv : LocalRatio D) (t : Wings u 1) (e r) :
    lunar X ν D t e r=feather (moon X ν D t.up e r) (Chain.predict G X t.N t.i)+dark X ν D e r t :=
   division ν (X.patch t.i) D X.kernel (X.trees t.i) (X.history t.N (t.i+1)) (h _) (rallies h hv t.up).totes.1 _ _
lemma dark_words (h : X.Wake G) (hv : LocalRatio D) (t : Wings u 1) : Glows (dark X ν D e r t) := by
  let T:= feather (moon X ν D t.up e r) (Chain.predict G X t.N t.i); have he := X.rawStep ν D h hv t.cut
  have hP : Glows (lunar X ν D t e r):= (he.1.2 _ _).2
  obtain ⟨p⟩:= lenders G X.kernel
  have ht:= warmer ((rallies (ν:=ν) h hv t.up).totes.gets.2 e r|>.2) (show Whole (Chain.predict G X t.N t.i) from ⟨_,_,p.wpos _,(report_funding X h p t.i t.N).2⟩)
  rw [show dark X ν D e r t=lunar X ν D t e r-T from by rw [obverse h hv t e r]; unfold T; abel] -- abel unfold?
  simpa only [neg_one_smul, sub_eq_add_neg,T] using hP.plus (ht.scale (-1))

-- diagonal diff & extension force troll
lemma tilt_sub (h : X.Wake G)(t : Wings u 1){F H : Pot G (r+2)}(he : Glows F)(hp : Glows H) :
   tilted X t ν (F-H)=tilted X t ν F-tilted X t ν H := by
   obtain ⟨Y⟩:= lenders G X.kernel
   have hQ : Whole (Chain.predict G X t.N t.i):= ⟨_,_,Y.wpos _,(report_funding X h Y t.i t.N).2⟩
   have hp₁:= warmer he hQ
   have hp₂:= warmer hp hQ
   apply Eq.trans _ (penny_sub ν _ r hp₁ hp₂); unfold tilted feather
   rw [gem_less he.summable hp.summable,scroll_less ((jewel _ he).summable) ((jewel _ hp).summable) (scan_whole hQ)]

-- strict same-rank forces

def morph (X : Chain) (t : Wings u 1) (ν : G.ColorIndex) (D : ChartRatio G) (r q : ℕ) : Pot G (r+2) :=
  match r with
  | 0 => duetT ν (lunar X ν D t) (orbit X t) (q-1)
  | s+1=> eclat ν (lunar X ν D t) (orbit X t) q s
lemma action_step (h : X.Wake G)(hv : LocalRatio D) (t : Wings u 1)(hp : 0 < r+2*q) :
    moon X ν D t.low (r+2*q) (r+2)=penny ν (orbit X t) r (lunar X ν D t (r+2*q) (r+2))+morph X t ν D r q := by
  cases r with
  | zero=> cases q with
          | zero=>omega
          | succ j=> erw [moon,X.album_step ν D t.cut]; simp only [Nat.zero_add,morph,Nat.add_sub_cancel]; exact deuce ν _ _ j (X.high_stocks ν t.N t.i).2.2 -- `q-1`
  | succ r=> erw [moon,X.album_step ν D t.cut]; exact tinder ν _ _ _ _
def dusk (X : Chain) (t : Wings u 1) (ν : G.ColorIndex) (D : ChartRatio G) (r q : ℕ) :=
  penny ν (orbit X t) r (dark X ν D (r+2*q) (r+2) t)+morph X t ν D r q
lemma stepped (h : X.Wake G)(hv : LocalRatio D)(t : Wings u 1) (ht : 0 < r+2*q) :
    moon X ν D t.low (r+2*q) (r+2)= tilted X t ν (moon X ν D t.up (r+2*q) (r+2)) +dusk X t ν D r q := by
  rw [action_step h hv t ht, obverse h hv t]; obtain ⟨Y⟩:= lenders G X.kernel
  rw [penny_add ν _ r (warmer ((rallies h hv t.up).totes.gets.2 _ _|>.2) (show Whole (Chain.predict G X t.N t.i) from ⟨_,_,Y.wpos _,(report_funding X h Y t.i t.N).2⟩)) (dark_words h hv t)]; unfold tilted dusk orbit; abel

-- sector predecessor budgets. Winks may only be supported songs *as
-- a context-free family; no need strict Ward witnesses from budgets here!
lemma smaller_sector {J : Type} {δ σ y : J→ℝ}{F H : J→Air G}{V U : J→Pot G 2}
    (h : G.Simple)(hf : ∀ i,RunsInk ν (V i) (F i))(hp : ∀ i,RunsInk ν (U i) (H i))
    (hs : Voucher y δ (V-U) σ)(hV : ∀ j p, RootStep 1 (r+2*q) (r+2) j p → Voucher y δ (fun i=> F i j p-H i j p) σ) (hk : s<r+2) : Voucher y δ (fun i=>(sector (V i) (F i) q-sector (U i) (H i) q) s) σ := by
  match s with
  | 0=> simp only [Pi.sub_apply,sector, sub_self]; exact Voucher.zero
  | 1=> simp_rw [Pi.sub_apply,sector, (hf _).waxed h,(hp _).waxed h,sub_self]; exact Voucher.zero
  | j+2=>
    by_cases he : j+2*q=0
    · rw [show j=0 by omega]; simp only [Pi.sub_apply,sector,show 0+2*q=0 by omega,↓reduceIte,prolong_self]; exact hs
    simp only [Pi.sub_apply,sector,if_neg he]; exact hV _ _ ⟨⟨by omega,q,by omega⟩, Or.inl (by omega)⟩
end YM.RG08.Wings
