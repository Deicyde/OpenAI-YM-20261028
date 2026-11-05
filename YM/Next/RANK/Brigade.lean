import YM.Next.RANK.Concord
import YM.Next.RANK.Orchid
import YM.Next.RANK.Possible
import YM.Next.RANK.Purchased

/-!
# Putting costs in a post-L waiting predicate

`readyHere` scale AND `window` before & after, and Bar post-L connections.
Numbers can be prepaid at specified requests (`Served`). Does not pluck an
allocated Family from a budget; when constructing one all the other post-L
conditions still need to agree and survive. Step/rooting constants `a` are
positive post-L. Numbers do not ensure ANY fields. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Tapes
open Function MeasureTheory Filter Asymptotics Lattice Wilson RG Perch Atlas Rise Normal Ribbon Spindle Glyph Exponential MvPolynomial Camp Peak Station Ac Alarm Thirst Corona Value Marker Cells Edition Finset Relation Paint Read RG.Supply Ship
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge}

-- era positivity a after L but Z.cost must be pre-L in these gates. Stamp(s) before.
structure Regiment (p : Purse) (S : Stage) (L : Side) : Prop where
  credit : p.budget
  bound : Digits p (L.val:ℝ)
  aptitude : stipend S p
  purchase : p.goal+4 ≤ p.taylor
  ability : p.horizon+10 ≤ p.era.coast.Q
  cockpit : 10≤ p.horizon
  radius : 128*p.era.coast.Q ≤ L.val

variable {p : Purse} {B : Stage}
-- after L, use Ribbon thresholds, cost goal number -3
structure SlotPrice (p : Purse) (d : ℝ) (G : Gauge) (B : Stage) (L : Side) (s : ℝ) : Prop where
  cost : Faring p s
  gauge m : m ≤ 2 → Awakening p s m (G:=G)
  forward : Racer p s (bump (↑L.val:ℝ) p.band s)
  room (T : Levels G) (i k) : clim T k=s → wheel T k=(L.val:ℝ) → Allowed T p.band k →
    (∀ i,Station.width T p.band k ≤ i → i≤k → clim T i∈Set.Icc (s/2) s) →
    roomTest T p.band k i p.horizon p.era.coast.Q
  fees : Ready (G:=G) (load p.era) p.era.coast.a s (-3) B
  asteroid : Rocket p.f (load p.era) (-3) p.era.coast.a p.goal p.era.coast.Q p.taylor d s B
  dating x : x ∈ Set.Icc (s/2) s → Ready (G:=G) (load p.era) p.era.coast.a x (-3) B
  money : B.columns ≤ Perch.bill (LiftMark.shade p.taylor/4) s
  order : p.taylor+1 ≤ B.order

lemma annually (L : Side) (d : ℝ) (h : Regiment p B L) (hd : 0≤ d) : ∀ᶠ s in atTop, SlotPrice p d G B L s:= by
  let a:= p.era.coast.a;let e:= load p.era; let Q:=p.era.coast;let Y:=p.taylor
  have hx: 0<a:= Q.posA
  have he:=h.aptitude
  obtain ⟨y,hy₀⟩:= eventually_atTop.mp (offering B (load p.era) _ (-3) h.aptitude.1 hx h.aptitude.2.1 (G:=G))
  filter_upwards [(Perch.half.eventually_ge_atTop y),funding p h.credit, (eventually_all_finset (range 3)).2 (fun m _=> awakens m p h.credit (G:=G)),racetrack _ h.bound,
    sizes_C p.band p.era.coast.Q p.horizon h.cockpit h.ability h.radius (G:=G), offering B _ _ (-3) h.aptitude.1 hx h.aptitude.2.1 (G:=G),
    rockets B Q.Q p.goal p.taylor p.f e (-3) a d (by norm_num) hx h.aptitude.1 (by linarith only [p.motion,p.fits]) hd h.purchase,
    (bill_lo (show 0 < LiftMark.shade Y / 4 by linarith only [LiftMark.shade_pos Y])).eventually_ge_atTop B.columns] with s hy hf hp hr hX ho hg hb
  exact ⟨hf,fun m h=> hp m (mem_range.mpr (by omega)),hr,fun i k m h g=> hX i k m g h,ho,hg,(fun x hx=> hy₀ x (le_trans hy hx.1)),hb,h.aptitude.2.2⟩

section scheduling
variable {X : Sheet G} {w : Rolls X} {D : Protection w} {T : Delays D} {Z : Bar T}

-- Keep all points actual when storing physical proofs. stamps from ramp still need Budget.Leg etc.
def ReadyRack (O : HaarBudget G) (j : ℕ) (p : Purse) (C : ℝ) (B : Wait Z) := Fired Z B O j p.band 2 p.era ∧ ∀ s : ℝ,
    B.readyHere j≤ s → SlotPrice p C G (X.profile j) (w.L j) (preHat Z s)

-- finite product tickets each commissioned before L. Ramp for charges can be monotone
lemma tabled (h : G.Simple) (B : Wait Z) (k : ℕ → Finset ℕ) (O : HaarBudget G) (G₀ : ℕ → ℕ → Purse) (M : ℕ → ℝ)
    (b : ℕ→ℝ) (hb : ∀ j,0≤ b j) (he : ∀ i,0≤M i) (hh : ∀ i j,(G₀ i j).band=b i) (hp : ∀ i j,i∈k j → Regiment (G₀ i j) (X.profile j) (w.L j)) :
    ∃ B' : Wait Z,B.minLength ≤ B'.minLength ∧ (∀ j,B.readyHere j≤ B'.readyHere j ∧ (∀ s,B.window j s ≤ B'.window j s)) ∧
      ∀ i j,i∈ k j → ReadyRack O j (G₀ i j) (M i) B':= by
  obtain ⟨W,hW,hZ,hv⟩:=served Z h O B (fun _=> 2) b (fun i j=> (G₀ j i).era) k (fun i=> by norm_num) hb
  have hl: Tendsto (preHat Z) atTop atTop:= Filter.tendsto_atTop_add_const_left _ _ (tendsto_id.const_mul_atTop (Gauge.slopeConstant_pos h))
  have ht (j) := (eventually_all_finset (k j)).2 (fun i hi=> hl.eventually (annually (p:=G₀ i j) (G:=G) _ (M i) (hp i j hi) (he i)))
  choose t hs using fun j=> eventually_atTop.mp (ht j)
  let p: Wait Z := { W with readyHere := fun j=> max (W.readyHere j) (t j) }
  refine ⟨p,hW,fun j=>⟨(hZ j).1.trans (le_max_left ..), (hZ j).2⟩,fun i j h=>⟨fun s hj=> ?_,fun s hk=>?_⟩⟩
  · rw [hh]; exact hv j i h s ((le_max_left _ (t j)).trans hj)
  exact hs j s ((le_max_right _ _).trans hk) _ h

lemma affords {C : Family G} {i n k : ℕ} (hG : G.Simple) (O : HaarBudget G) (p : Cohesion C i) (B : Wait Z) (h : Paid B C.path.levels)
    (hX : ReadyRack O n (p.purses n) p.mark B) (he : X.first<n)
    (hk : C.path.levels.clock.J k=n) (hv : B.readyHere n ≤ C.S.scale k) (hu : B.window n (C.S.scale k) ≤ k)
    (hz : ∀ i,k-B.window n (C.S.scale k) ≤ i → i≤k → C.path.levels.clock.J i=n) :
    Metering p O k (-3) ∧ ∀ j, roomTest C.path.levels (p.current k).band k j (p.current k).horizon (p.current k).era.coast.Q := by
  obtain ⟨V,H⟩:=hX; let a:= C.path.levels; let Y:=a.clock; let P:=p.purses n
  have ht: Charge a P.band k 2 O P.era:= held_at B a h he hk hv hu hz O 2 P.band P.era V hG
  have hS:= H _ hv; let s:=clim a k;let e:=Y.stage n
  have hℓ:a.params k=X.profile n:=by change Y.stage (Y.J k)=_; rw [hk,show Y.stage=_ from h.stage]
  have hh: P=p.current k:= by unfold Cohesion.current;rw [hk]
  let L := (w.L n).val
  have hP : wheel a k=L:=by unfold wheel; rw [show a.clock.factor= _ from h.lengths,hk]
  have hf : preHat Z (C.S.scale k)=s:= by unfold preHat; change _=Calendar.hatBeta a.clock k;rw [Calendar.hatBeta,h.bar]
  have H : SlotPrice P p.mark G (a.params k) (w.L n) s := by rw [hℓ,← hf]; exact hS
  have hE : p.fixed=P.band:= (p.sameB _).symm
  have HZ : ∀ i,Station.width a P.band k ≤ i → i ≤ k → clim a i∈Set.Icc (s/2) s:= by
    intro i hi hm;let l:=middle a P.band k
    have hx t u(h:t≤u):clim a t≤clim a u:= by
      unfold clim Calendar.hatBeta; gcongr
      · exact (Gauge.slopeConstant_pos hG).le
      have hv b : a.S.scale b ≤ a.S.scale (b+1):= by rw [a.S.scale_succ]; exact le_add_of_nonneg_right (Real.log_nonneg (by exact_mod_cast (a.S.block b).property))
      exact monotone_nat_of_le_succ hv h
    have hi':=ht.assured l (Station.wider a P.band k) le_rfl
    rcases le_or_gt i l with h|h
    · exact ht.assured i hi h
    exact ⟨hi'.1.trans (hx _ _ h.le),hx _ _ hm⟩
  have hD:=ht.allot.permitted; have hF:= hD.full
  have hr:Racer P s (k-middle a P.band k):= by rw [hF,height,hP]; exact H.forward
  have hl: Launch C k P (-3) p.mark:= ⟨H.fees,H.money,H.order,H.asteroid,⟨ht.allot.permitted,hr,H.cost,HZ⟩,fun i=> H.gauge i⟩
  refine ⟨⟨?_,hh▸ hl⟩,?_⟩
  · have hz': Charge a p.fixed k 2 O P.era:= hE ▸ ht
    exact hh ▸hz'
  intro j; rw [← hh]; exact H.room _ j k rfl hP hD HZ

end scheduling
end YM.Next.Rank.Tapes
