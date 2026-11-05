import YM.PhysicalNext.AFTERNOON_INTERACTING_RANK_COMPARISON.Soft.Corona

/-!
# Variant of the Provisions port

Adapt the `Next/RANK` argument from here to these weaker
ancillary demands only.

Not modifying `C.Makes`, all still true Regular
& pulse on the actual physical history.

Also preserves the Stake tests.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.InteractingRank.Soft
open Function MeasureTheory Filter Lattice Wilson RG Next.Rank Next.Rank.Tapes Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation Paint Vac.Numbers Read
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius
variable {G : Gauge}
variable {C : Family G} {i k l j m p q d D a N : ℕ} {S : Table C.book}

variable (F : Cohesion C d) (W : HaarBudget G) (P : Columns C S d)

variable (H : C.Makes)

-- Keep visible mathematical checkpoint. This does NOT assert density Comparison.
def s_supplies {w} (p₀ : Launch C k (F.current k) w F.mark) :=
    let A:= C.path.levels; let s:= clim A k; let D:=F.current k
    ∀ (hk : C.ref d ≤ k),(∀ i,Fit C.path.levels D.band k (P.row i).expected) →
      ∀ᶠ N in atTop,∃ (hN : k ≤ N), ∀ p, ∃ (X : AtlasData G C.S p) (T : Lead G C.S p) (c : Course C N p k) (Y : (u : ℕ)→Rep G (C.side u p)),
        survivors C N k p p₀.pane (Y k) ∧ Nylon c Y X T D ∧
          ∀ i, Crew c Y T D (P.row i).expected ∧ Wall.Vantage A d k p ((P.row i).extra+1) F.atoms F.fixed X ∧
            ∀ V : Fin ((P.row i).extra+1)→ C.label d, (∀ j, Perch.bill F.pan s*moneys C d k N p (V j)≤ Perch.bill (-8) s) →
              Stake (P.row i).extra (P.row i).expected D.band hN V H hk c (Hat s ^ F.mark)

-- simultaneous demands before comparison (post-L gates and actual existence of all these inputs on these k stamps)
def s_provisions := ∃ᶠ k : ℕ in atTop, ∃ w : ℝ, ∃ U : Metering F W k w, s_supplies F P H U.cost


-- Although Screen needs Ferm at width, keep the ancestral Path to middle
def Path_ {k N p}(Y : Course C N p k)(R : (u:ℕ)→Rep G (C.side u p))(hN : k≤N)(b : ℝ):Prop:=
    ∀ u, width C.path.levels b k ≤ u → ∀ h : u ≤ middle C.path.levels b k,
      Novice Y u (R u) (h.trans ((before C.path.levels b k).trans hN))
def s_empire (O : HaarBudget G) (D' : ℕ → Era) (P : Columns C S d) (u : Price.Representatives C P) (b : ℝ) (deg : ℕ) : Prop := ∃ᶠ k : ℕ in atTop,
    let Y:= C.path.levels; let B:= D' (Y.clock.J k)
    Charge Y b k 2 O B ∧ (C.ref d≤k → (∀ i,Fit Y b k (P.row i).expected) → ∀ᶠ N : ℕ in atTop,∃ hN : k ≤ N, ∀ p : ℕ,
      ∃ (X : AtlasData G C.S p) (M : Heater C k d) (read_ : C.label d →ₗ[ℂ] C.label d) (c : Course C N p k) (R : (u : ℕ) → Rep G (C.side u p)),
        Path_ c R hN b ∧ Heating C k N p d deg M read_ ∧ ∀ i (h : Fit Y b k (P.row i).expected),
          Bell Y X d deg h ∧ ∀ v, Price.Names C u (Station.mag Y b k) k N p read_ v → ∀ j,
            Clipped b X M c R (P.row i).expected (uses P v i j) hN deg B.coast 2 ∧
              Exhibits c R b (P.row i).expected 2 hN (Ship.invoice (joint (uses P u.rep i j)) (asked (uses P v i j)) h N p) B)

-- assembly proof
variable (v : Price.Representatives C P)


lemma v_paid_factory (h : G.Simple) (Hp : s_provisions F W P H) : s_empire W (fun j=> (F.purses j).era) P v F.fixed F.atoms:= by
  let A:=C.path.levels
  have hb := Cohesion.hr F
  have he:= eventually_all.mpr fun i=> Wall.on_demand A F.fixed F.atoms d h (generic_conf _ (P.row i).probes) F.large
  have hc:= eventually_all.mpr fun i=> eventually_all.mpr fun j=> boot (Atlas.uses P v.rep i j) h H F.mark (P.row i|>.expected) (P.row i|>.probes) F.fixed F.pan hb F.money F.atoms
  have hr:= eventually_all.mpr fun i => StampDuty.procure C h H d F.atoms (v.rep i) F.fixed hb F.pan F.money
  refine (Hp.and_eventually (he.and (hc.and (hr.and (forge C h H _ _ F.numbers))))).mono ?_
  rintro k ⟨⟨w,U,hU⟩,hC,hV,hR,hT⟩
  refine ⟨U.charge,fun hL hΦ=> ?_⟩
  let J:= A.clock.J k; let P':= F.purses J; let b:=P'.era
  have hz : P'=F.current k:=rfl
  have hK:P'.band=F.fixed:= F.sameB J
  filter_upwards [hU hL (by intro i; rw [← hz,hK]; exact hΦ i)] with N hn
  obtain ⟨hN,HN⟩:=hn; refine ⟨hN,fun p=>?_⟩
  obtain ⟨X,T,c,Y,hy,hy',V⟩:= HN p
  have hh:= hy'.fixture (before ..) (le_refl k)
  have hF : P'.taylor=F.atoms:= F.same_size J
  have hg : year C F.atoms k:= hF ▸ (show year C P'.taylor k from U.cost.year)
  have hx : Hail C k p P'.taylor X:= hy'.stencil
  have ht : 8 ≤ b.coast.Q := by
    have hv: (F.current k).horizon + 10 ≤ b.coast.Q:= hy'.paths.canvas.radius; omega
  have hY : Nonempty (StampDuty C k N p d P'.taylor (Y k) b.coast.Q X):= by
    have hx' := hT hL hg (show F.atoms+1 ≤ _ from hF ▸ show P'.taylor+1 ≤ _ from U.cost.length) N p hN (Y k) b.coast.Q hh.threshold hh.budget ht X (hF ▸ hx)
    rw [hF]; exact hx'
  obtain ⟨M⟩:= hY; let s:=clim A k; let ξ:= M.heater
  have hP : Path_ c Y hN P'.band:= fun i h H=> hy'.use_ _ h (H.trans (before ..))
  refine ⟨X,ξ,M.T,c,Y,hK ▸ hP,hF ▸ M.lights,fun i hr => ⟨?_, fun u hΩ j=> ?_⟩⟩
  · exact hC i hr U.charge.allot.permitted p X (V i|>.2.1)
  let θ:=P.row i;let K:= Atlas.uses P u i j; let v₀:= Atlas.uses P v.rep i j
  have hs: Fit A P'.band k θ.expected:= by rw [hK]; exact hΦ i
  have he : Crew c Y T P' θ.expected:= (V i).1
  have hi : θ.extra+1≤2:= by have h := θ.cap; omega
  have hz : Boot k d P'.taylor F.mark θ.extra P'.band P'.f θ.expected v₀ H:= by rw [hF,hK,F.funding J]; exact hV i j
  have hW (a): Price.Solves C (mag A P'.band k) d k N p M.T (v₀ a) (K a):= by rw [hK]; exact hΩ _
  have hp : Stake θ.extra θ.expected P'.band hN K H hL c (Hat s ^ F.mark):= by
    apply (V i).2.2 K; intro a
    let b:=Columns.Trials.names (X:=P) i j a; let r:= Perch.bill F.pan s
    let Q : Prop:= r*moneys C d k N p (u b)≤Perch.bill (-8) s
    -- cast schedule
    have hm : ∀ {Q B X} (M : StampDuty C k N p d P'.taylor Q B X) (p₀) (_ : Price.Solves C (mag A F.fixed k) d k N p M.T (v.rep b) p₀),
          r*moneys C d k N p p₀ ≤ Perch.bill (-8) s:= ?_
    · exact hm M (u b) (hK ▸ hW a)
    rw [hF]; intro _ _ _ M p ht; exact (hR b hg N _ hN M p ht).1
  have hs' : Clipped P'.band X M.heater c Y θ.expected K c.allow P'.taylor P'.era.coast 2:= v_stir hy' M H hL U.cost hy hs v₀ hz (F.credit (A.clock.J k)) hi K hW hp he
  refine ⟨hF ▸ (show Clipped F.fixed X _ _ _ _ _ _ P'.taylor _ _ from hK ▸ hs'),?_⟩
  let f:= (Ship.invoice (joint v₀) (asked K) hr N p)
  have hp':Exhibits c Y P'.band _ 2 hN f P'.era:=turnWheel U.cost.coup.heft U.charge.tally he f
  rw [hK] at hp'; exact hp'
end YM.PhysicalNext.InteractingRank.Soft
