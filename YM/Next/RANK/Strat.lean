import YM.Next.RANK.Stall

/-!
# Restrict upstream multi preparation input to genuine needed moments

All signed tags with ≥2 still input from RMixed/RBin path. This case strictly
prior: at OLD threshold, OLD radius, OLD labels, ANY given Xi in coefficient
families. Actual callers need estimates on a specified family (or their
values with supplied budgets), after choosing finite labels by .$Income. No
raw asserted plateau root estimates. Identity off-height path independent.
This file: all foil labels below that tag arity computed exactly from coherent
basis choices at OLD k, no limit or ignored orders. -/
set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.Edition
open Function Filter RG Thirst Lattice Wilson MeasureTheory Relation Corona Value Glyph Marker Perch Vac.Numbers Alarm Spindle Station Cells Atlas Finset Baler Source
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius

variable {G : Gauge} {n : Side} {A : Activities G n} {Q : Rep G n} {V κ ι : Type} [DecidableEq V] [Fintype V]
variable {C : Family G}
variable {d k N p c m : ℕ}

lemma sym_eval (T : Course C N p k) (m : ℕ) (H : C.Makes) (hm : m≤N) (hp : k≤m) (u : Config G (C.side m p)) (s : Signed) (x : Site (C.side m p)) : (C.path.rep N p m).eval (pull s x u)=(C.path.rep N p m).eval u:= by
  -- use explicit R symmetry of eval/exponent and gas from Moves (works even at flags). alternative Course flow_linear
  let W := bare (G:=G) (n:=C.side N p) (C.beta N p)
  let R := Complex.ofRealCLM
  let F:= R∘W
  have hs : Integrable W (prior G _):= bare_integrable _
  have he := flow_sym T F (R.integrable_comp hs) s m hm x
  have hy : F∘pull s ((C.S.toDepth hm p).embed x)=F:=funext fun x=>congr_arg R (bare_pull ..)
  rw [hy] at he
  have ha := T.flow_linear W R hs m hm
  change R∘T.vacuum m hm=T.flow _ m hm at ha
  rw [T.vacuum_at H m hm hp] at ha
  change T.flow F m hm=(T.flow F m hm)∘_ at he; change R ∘ _=T.flow F m hm at ha
  rw [← ha] at he; exact Complex.ofReal_injective (congr_fun he u|>.symm)

variable (X : Points (m+1)) (hN : k≤N) (s : ℝ) (t : Fin (m+1) → C.label d)

-- spelling input for RMixed: W copies and K already fixed. Proof of equality of credentials at *any* subword.
section
variable (Z : Neat (C.side k p) → Burst G (C.side k p) (C.path.rep N p k).p.threshold)

def press (i : Listens C s (v:=m+1) hN p) := parcel C d k N p (t i.2)
lemma satisfies (i : Listens C s (v:=m+1) hN p) (h : C.Makes) (hp : C.ref d≤ k) : (press hN s t i).Format 0 C.params (C.path.rep N p k):=
    (h.calibrated d N p (hp.trans hN)).format k hp hN _
variable [Fintype κ] [Fintype ι] (A : ι → SourceAt G (seats C s X hN p))
variable (B : κ→Lifted G (seats C s X hN p) (C.path.rep N p k).p.threshold)

def fabricated (h : C.Makes) (hp : C.ref d ≤ k) := creds Z (press hN s t) (pinHat C d k) (fun i=> satisfies hN s t i h hp) (hand C s hN p) (fp C s hN p) B A (C.localSection d)

def ensembleO (h : C.Makes) (hp : C.ref d≤ k) := elder (seats C s X hN p) Z (press hN s t) (pinHat C d k) (fun i=> satisfies hN s t i h hp) (hand C s hN p) (fp C s hN p)

lemma prepaid (Y : Course C N p k) (h : C.Makes) (hp : C.ref d ≤ k)
    (he : IsoVac _ Z (C.path.levels.clock.forcedAllowance k)) (χ : ∀ U : Config G (C.side k p),∀ v,2 ≤ (v.val:Finset (Listens C s hN p)).card →
      (fabricated X hN s t Z A B h hp U).part v=(Bills C s X hN p t Y U).part v)
    (hA : ∀ i,2≤(A i).fires.val.card) (hB : ∀ i,2≤(B i).fires.val.card) :
    Bills C s X hN p t Y=fabricated X hN s t Z A B h hp := by
  ext1 U; let P:=C.path.rep N p k; let K:=Bills C s X hN p t Y U; let L:=fabricated X hN s t Z A B h hp U
  let V:=Listens C s (v:=m+1) hN p; let T:= C.factory d N p
  have he' := h.calibrated d N p (hp.trans hN)
  have HX (i : V) : L.part (quiet _)= (P.eval (puller C s X hN p i U):ℂ) ∧
      L.part (slot i) = dot (fp C s hN p i) (pinHat C d k * ((press hN s t i).density 0 (C.localSection d) P (puller C s X hN p i U))) := by
    apply why Z (press hN s t) (pinHat C d k) (fun i=> satisfies hN s t i h hp) (hand C s hN p) (fp C s hN p) B A he hB hA i U (h.wilson.represents _ _ _ hN).good (show (press hN s t i).remBound 0 P _ _ from he'.cap k hp hN _) (C.localSection d)
  refine Eq.symm (Poly.ext (f:=L) fun i=>?_)
  by_cases ht : 2 ≤ (Finset.card (Subtype.val i))
  · exact χ U i ht
  rcases hV: i.val.eq_empty_or_nonempty with hv|hv
  · rw [show i=quiet V from Subtype.ext hv]; let z : V := (0,0)
    exact (HX z|>.1).trans ((congr_arg Complex.ofReal (sym_eval Y k h hN le_rfl U ..)).trans (congr_fun (s_quiet C s X hN p Y h t) U |>.symm))
  obtain ⟨x,hx⟩:= card_eq_one.mp (show i.val.card=1 by have hl:=card_pos.mpr hv;omega)
  rw [show i=slot x from Subtype.ext hx]; exact (HX x|>.2).trans (congr_fun (s_single C s X hN p Y h t hp x) U|>.symm)
end
end YM.Next.Rank.Edition
