import YM.WilsonBulk.Broadcast.Summit

/-!
# Coherent positive joint/finite pressure. Form in coupling of the INPUT.

Costs: only structural assumed: real `Branches`, true moment-width analyticity
of V (before lengths supply elsewhere), LocalRatio J around exp. I is FULL
input, leading summit checked at period, do not carry absolute constant.
`arises` will choose larger ports only for symmetry passage; output prescription
uses maximal unmasked `lifted`, ratio κ, actual repeated tree, conditional log
on cover (cashless), NOT finite scalar limits. Finite pressure proof includes
finite scalar. No kinetic reset yet. Keep separate for interactions/extraction.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk.Parapet
open scoped Topology Classical BigOperators ENNReal ContDiff Matrix.Norms.Frobenius
open Lattice Laurent Filter Equiv Function Bloch Matrix Precision Stationary Audience Exterior Wilson
open Work.F08 RG Sheet Pert.Bulk Atelier FreeResolvent
open Work.F08 Lifted
open PowerSeries (constantCoeff coeff)
variable {c f L : Side} {G : Gauge} {S : StepData c f} {P : Patch} {K : KernelChoices}
variable {θ σ p : ℝ}

abbrev Library (G : Gauge) := Record (Market (Cloth G))
abbrev Printed (G : Gauge) (P : Patch) := Record (Market (Wharf G P)) -- maybe unused
abbrev oil (G : Gauge) (P : Patch) := install (varnish P.L (Cloth G) (Cloth G))
def dais (J : ChartRatio G) (P : Patch) (K : KernelChoices) (I : Library G) : Printed G P := lecture (oil G P) (curtainHair J) - noisePart P K G - lecture (oil G P) (later I)
lemma podium_style (J : ChartRatio G) (P : Patch) (K : KernelChoices) {I : Library G} (h : Document I) : Document (dais J P K I) := by
  refine (((chapters_here 0 _ (tariffJ J) (by omega) rfl).board _).lectured (oil G P) |>.minus ((chapters_here 2 _ (splatter P G K.penalty) le_rfl rfl).board _)).minus ((h.board _).lectured _)
lemma oilSession (G : Gauge) (P : Patch) (n) : Session (oil G P) n := installSession (varnish_cost _ _) one_pos zero_le_one
lemma podium_hears (J : ChartRatio G) (P : Patch) (K : KernelChoices) {I : Library G} (h : Pamphlet I) : Pamphlet (dais J P K I) := by
  have hU (x : Library G) (hx : Pamphlet x) i j : Public (lecture (oil G P) x i j):= Public.travel (oilSession G P _) (fun z=> P.L.val • z) (fun u v b=> install_roll _ _ _ _) (hx _ _)
  exact Pamphlet.minus (Pamphlet.minus (hU (curtainHair J) ((chaptersPublic 0 _ _).board _)) ((chaptersPublic 2 _ _).board _)) (hU _ (h.board _))
lemma podium_free (J : ChartRatio G) (P : Patch) (K : KernelChoices) (I : Library G) : Sheet.Free (dais J P K I) := (((Sheet.Free.later _).lectured (oil G P)).minus (Sheet.Free.later _)).minus ((Sheet.Free.later _).lectured _)

-- expression in leading matrix terms independently of spectator. Use advanceP price
lemma move_height {I : Tape (Pennant G f)} :
    submit (exposure (upper (Pennant G f) (Pennant G c))) (advanceP _ I) = advanceP _ (submit (exposure (upper (Pennant G f) (Pennant G c))) I) := by
  rw [upper_code]; change submit (named ∘ Sum.inl) (advanceP _ I) = advanceP _ (submit (named ∘ Sum.inl) I) -- need implicit β
  rw [submit_name,submit_name]; ext1 i; cases i
  · rw [advance_zero, coeff_parallel,advance_zero,map_zero]
  rw [advance_hr,coeff_parallel,coeff_parallel,advance_hr]
lemma stoic {B : Bed} :
    advanceP _ (ambient (matrixK G f B) (probeX G S) S.kernel.penalty)=0 := by -- B unbound declare
  let F:= forceQ (matrixK G f B) (fun i=> (privateName (ι:=Pennant G c)) i)
  let H:= breach G S (privateName (ι:=Pennant G c)) viewer
  change advanceP _ (F+H)=0
  have hp : F+H=PowerSeries.C ((forceQ (matrixK G f B) (fun i=> MvPolynomial.X (Sum.inl i))) + static G S):= by rw [map_add, show F =_ from force_top (matrixK G f B),pay_breach (G:=G)]
  rw [hp]; simp [advanceP]

lemma anchor {A : Type} [CommRing A] (p q : PowerSeries A) (he : Steps 1 p q) (hq : advanceP _ q=0) : advanceP _ p=p-q := by unfold advanceP at *; rw [(steps_initial ..).mp he,← sub_eq_zero.mp hq]
lemma anchor2 {A : Type} [CommRing A] (p q r z : PowerSeries A) (h : advanceP A (p+q)=p+q-r) : z-advanceP A q-advanceP A p= -(p+q)+r+z := by
  rw [← sub_add_eq_sub_sub_swap]; rw [← show advanceP _ (p+q)=advanceP _ p+advanceP _ q from ?_,h]; abel
  unfold advanceP; rw [map_add,map_add]; abel
variable {J : ChartRatio G}
variable (t : S.Choices) (I : Library G) (B : Bed)
abbrev audienceK (G : Gauge) (n : Side) (I : Library G) := volumeTape (Sheet.issue n I)
lemma podium_ambience (hl : S.patch.Branches S.kernel G) (hp : Pamphlet I) (hJ : LocalRatio J)
    (h : Steps 1 (audienceK G f I) (grains (matrixK G f B))) :
    jury (parade G S.ratio).symm (volumeTape (Sheet.issue c (dais J S.patch S.kernel I)))= curtain (matrixK G f B) (probeX G S) S.kernel.penalty (auditorium S t (audienceK G f I)) (haarTape c f J) := by
  let A:=oil G S.patch; let V:=lecture A (curtainHair J); let N:= noisePart S.patch S.kernel G; let U:=lecture A (later I)
  have hV : Pamphlet (curtainHair J):=(chaptersPublic 0 _ _).board _; have hL : Pamphlet (later I):=hp.board _
  have hX (u : Library G) (hv : Pamphlet u) : Pamphlet (lecture A u):= fun i j=>Public.travel (oilSession G S.patch _) (fun z=>S.patch.L.val • z) (fun x y b=>install_roll ..) (hv _ _)
  have he := auditorium_start (P:=B) t hl h
  have hi : advanceP _ (auditorium S t (audienceK G f I))= auditorium S t (audienceK G f I)-ambient (matrixK G f B) (probeX G S) S.kernel.penalty:= by
    apply anchor _ _ he stoic
  change jury _ (volumeTape (Sheet.issue c (V-N-U)))=_
  have hN : Pamphlet N:= (chaptersPublic 2 _ _).board _; rw [show Sheet.issue c (V-N-U)=_ from Pamphlet.issued_minus c ((hX _ hV).minus hN) (hX _ hL), show Sheet.issue c (V-N)= _ from (hX _ hV).issued_minus c hN,tape_minus,tape_minus,map_sub,map_sub]
  let D:= (jury (parade G S.ratio).symm)
  let W:= mountain (Pennant G f) (Pennant G c)
  have hU : D (volumeTape (Sheet.issue c U))=W (advanceP _ (audienceK G f I)) := (varnish_lecture (β:=Cloth G) S.ratio _ hL).trans (by rw [later,← issue_board]; exact congrArg W (advance_board _))
  change D (volumeTape (Sheet.issue c V))- D (volumeTape (Sheet.issue c N))-D (volumeTape (Sheet.issue c U))=_
  rw [show D (volumeTape (Sheet.issue c U))= _ from hU, show D (volumeTape (Sheet.issue c N))=_ from jury_noise hl t, show D (volumeTape (Sheet.issue c V))=_ from ((varnish_lecture (β:=Cloth G) S.ratio _ hV).trans (veil_cash c f hJ))] -- D unfolds?
  let D':= exposure (upper (Pennant G f) (Pennant G c)); rw [show W=submit D' from by unfold W D' mountain; rw [upper_code]]
  erw [move_height (G:=G) (c:=c)]; exact anchor2 _ _ _ _ hi -- unfolds maybe large
end YM.WilsonBulk.Parapet
