import YM.RG08.Apex.Tips
/-! # Restrict to admitted grade. Limit exhaled, independent raw recursion.
Limit only taken *after* including tree-cov in coefficient program. -/
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Summit
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums UVExtension.Free
open scoped BigOperators Topology Real Classical
open Chain Wings
variable {X : Chain}{G : Gauge}{K : KPrices X.kernel}{g:KGate K}{P : Lending G X.kernel}{E : ℕ}{S : Prism G X.kernel g P E}{ν:G.ColorIndex}{D:ChartRatio G}{L : Side}
variable {I : Type} {u : I→Windows} {r e j s : ℕ}

-- purely grade dependence; enough even beyond support.
lemma leeks {α : Type} [Fintype α] (M : Row α α) (p : Option Side){F H : Canticle α}(h : ∀ e ≤ E,∀ r,F e r=H e r) (i)(he:e ≤ E)(r) : Refrain M F p i e r=Refrain M H p i e r := by
  induction i using Nat.caseStrongRecOn generalizing e r with
  | zero=> rw [Refrain,Refrain]; exact h e he r
  | ind i ih=>
    rw [Refrain_step,Refrain_step,ih i le_rfl he]; congr 3 -- sums
    apply sum_congr rfl; intro j hj; apply sum_congr rfl; intro k hk; have hp := mem_antidiagonal.mp hj; have hh:= mem_antidiagonal.mp hk
    rw [show Refrain M F p j.1 k.1=Refrain M H p j.1 k.1 from funext fun _=> ih _ (by omega) (by omega) _,show Refrain M F p j.2 k.2=Refrain M H p j.2 k.2 from funext fun _=> ih _ (by omega) (by omega) _]
lemma terrace_local (M : Row (Fink G L) (Fink G L))(Q : Row (Fink G L) (Loc G 1))(p : Option Side){F H : Canticle (Park G L)}(h : ∀ e ≤ E,∀ r,F e r=H e r) (he:e ≤ E)(r) : exhale M Q F p e r=exhale M Q H p e r := by
  unfold exhale upswell; simp_rw [leeks _ p h _ he]
def graving {α : Type}(E : ℕ)(F : Canticle α) : Canticle α := fun i j=> if i≤ E then F i j else 0
lemma granite_local (i : G.ColorIndex)(P : Patch)(M:Row (Fink G P.L) (Fink G P.L))(Q : Cross P.L (Loc G 1) (Loc G 1))(κ:ℝ)(D:ChartRatio G)(F:Air G)(he:e≤E) (r) : exhale M Q (awakening i P D κ (graving E F)) none e r=exhale M Q (awakening i P D κ F) none e r := terrace_local _ _ _ (fun i hi j=> by unfold awakening graving; rw [if_pos hi]) he r

-- independent rows version of `obverse`
lemma tideSplit (i:G.ColorIndex)(P:Patch)(M:Row (Fink G P.L) (Fink G P.L))(Q:Cross P.L (Loc G 1) (Loc G 1))(κ:KernelChoices)(D : ChartRatio G)
    (h : Whole M)(hp : Whole Q){F:Air G}(he:Gets F)(e r) :
    exhale M Q (awakening i P D κ.penalty F) none e r=feather (F e r) Q+scramble i P D κ M Q F e r:= by
  let U := awakening i P D κ.penalty F; have hu:= Gets_awake P D κ i he
  let Y := upswell (veiled M) U none 1 e r; let T:=afterT (veiled M) U none 1 e r
  let B := gemL P.L (F e r); let V:=luggage i P D κ e r
  have hY:Summable Y:=(upswell_deck (veiled M) (veiled_whole h) U (fun a b=> (hu.2 a b).1) hu.1 none 1|>.2 e r).1
  have hh : Y+B=V+T:=by unfold Y; rw [soothe]; change U e r+T+B=_; rw [show U e r=V-B from nuts ..]; abel
  change -scrollL Y (scan Q)=scrollL B (scan Q) + -scrollL (V+T) (scan Q)
  rw [← hh,scroll_more hY (gem_tune _ _ (he.2 e r).1.1|>.1) (scan_whole hp)]; abel

lemma grapes_get (P : Air G) (he : Gets P) : Gets (graving E P) := by
  refine ⟨fun i j=> ?_,fun i j=>?_⟩; · intro hp; unfold graving at hp; split at hp; exact he.1 i j hp; contradiction
  unfold graving; split; exact he.2 i j; exact ⟨Tunable.zero ..,Glows.zero⟩
lemma graving_stop (P : Air G){A:ℕ→Air G}(h : ∀ i,Gets (A i))(hv : ∀ e≤ E,∀ r,Mending (fun i=> A i e r) (P e r)) : Gets (graving E P) := by
  constructor
  · intro i j hj; unfold graving at hj; split at hj
    · rename_i he; by_contra hp; have ht s := not_ne_iff.mp (mt ((h s).1 i j) hp)
      exact hj (tendsto_nhds_unique_of_eventuallyEq (hv i he j).played tendsto_const_nhds (.of_forall ht))
    contradiction
  intro i j; unfold graving; split; next he=> exact ⟨(hv i he j).sing (fun _=> (h _).2 _ _|>.1),(hv i he j).1⟩
  exact ⟨Tunable.zero ..,Glows.zero⟩

def escalates (t:Launch u)(i:ℕ): Wings u 1 := ⟨t,t.i+1+i,t.i+1+i,(by omega),le_rfl⟩
lemma bye (X : Chain)(t:Launch u) : Tendsto (fun i=> chop X (1/4) (escalates t i)) atTop (𝓝 0) := (tendsto_gain X.S (v:=1/4) (by norm_num) t.i).comp ((show StrictMono (fun i=>t.i+1+i) from fun _ _ hh=>by simpa using hh).tendsto_atTop)
lemma successor (t:Launch u) (h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple) : Gets (graving E (statue X ν D (t.i+1))) := by
  let f n:= (escalates t n).up
  refine graving_stop _ (A:=fun i=> moon X ν D (f i)) (fun i=> (rallies hp hv _).totes.gets) fun e he r=>?_
  have ht:= (bothUp h (statues h hp hv hs he r)).mold (escalates t); exact Both.mended (y:=Launch.farY X t) (δ:=fun i=>chop X (1/4) (escalates t i)) (B:=Tier S (t.i+1)) ht (fun _=> (gain_pos ..).le) (bye X t) (S.positive _)
private lemma pursuit (h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple)(he:e≤E)(hk:r ≤ e+2) : Both (menu X)
    (chop X (1/4))
    (fun t:Wings u 1=> lunar X ν D t e r)
    (fun t=> exhale (slate X G t.i) (amber X G t.i) (awakening ν (X.patch t.i) D X.kernel.penalty (graving E (statue X ν D (t.i+1)))) none e r) (fun i=>Tier S i.i) := by
  let F t:= moon X ν D (t:Wings u 1).up; let V t:=graving E (statue X ν D ((t:Wings u 1).i+1))
  let L (t:Wings u 1):= X.patch t.i
  let η t:=ticketW P (X.J (t:Wings u 1).i)
  let M (t:Wings u 1):= slate X G t.i; let Q (t:Wings u 1):= amber X G t.i
  have hF e (he:e≤ E) r: Both (menu X) (chop X (1/4)) (fun i=> F i e r) (fun i=> V i e r) (fun i=> Tier S (i.i+1)):= by simp only [V,graving,if_pos he]; exact bothUp h (statues h hp hv hs he r)
  have hV t: Gets (V t):= successor (toLaunch t) h hp hv hs
  let W t:= scramble ν (L t) D X.kernel (M t) (Q t) (V t) e r
  have hQ:=polishes h hp; have hM:= smooth h hp; have hP:0≤ chop X (u:=u) (r:=1) (1/4):=fun i=> (gain_pos ..).le
  have hW : Both (menu X) (chop X (1/4)) (dark X ν D e r) W (fun i=> Tier S i.i) :=
    harvest_g (F:=F) (H:=V) (h.M.move toLaunch) hP (fun _=> ticket_pos ..) hM hQ (show _ ≤ _ from fun i=> S.strict_event _) he hk (fun _=> S.positive _) (fun _=>(S.positive _).le) (hire h) (fun _=>(rallies hp hv _).totes.gets) hV (fun i j hj=> hF i (le_trans (hj.2.elim (fun h=> h.le) (fun h=> h.1.le)) he) j)
  have ht := gem_accrue (L:=fun i=> X.S.block (Wings.toLaunch i).i) r (h.M.crop.transfer toLaunch) (sh X) (show 0≤η from fun i=> (ticket_pos ..).le) (fun i=> min_le_right ..) (fun _=>(S.positive _).le) (fun i=> (smul_le_smul_of_nonneg_right (show r+1 ≤ E+3 by omega) (ticket_pos ..).le).trans (hire h i)) (hF e he r)
  have hy:= remit (w:=fun i:Wings u 1=> Tier S i.i) (fun _=>S.positive _) (sh X) hP (ht.soften (fun _=> ticketV S (by omega) _)) (scanned_contract hQ (fun _=> ticketV S (by omega) _) (sh X) hP) (Weighed.constant _ (Nat.cast_nonneg (Fintype.card (Loc G 1)))) -- eta implicit
  simp_rw [obverse hp hv];
  rw [show (fun t:Wings u 1=> exhale (slate X G t.i) (amber X G t.i) _ _ e r)=(fun t=>feather (V t e r) (Q t)+W t) from funext fun t=> tideSplit ν _ _ _ _ D (hM.again.status (fun _=> ticket_pos ..) _) (hQ.again.status (fun _=>ticket_pos ..) _) (hV t) _ _]
  exact hy.add hW (sh X)
lemma grantPass (t:Launch u) (h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple) (he:e≤E)(r) : Mending (fun i=> lunar X ν D (escalates t i) e r) (granite X ν D t.i e r) := Both.mended (δ:=fun i=> chop X (1/4) (escalates t i)) (y:= t.farY X) (B:=Tier S t.i) ((graces h hp hv hs he r).mold (escalates t)) (fun _=> (gain_pos ..).le) (bye X t) (S.positive _)
theorem neighboring (t:Launch u)(h:Circuit S ν D u)(hp:X.Wake G)(hv:LocalRatio D)(hs:G.Simple)(he:e≤E)(r) :
    granite X ν D t.i e r = exhale (slate X G t.i) (amber X G t.i) (awakening ν (X.patch t.i) D X.kernel.penalty (statue X ν D (t.i+1))) none e r := by
  have hG := grantPass t h hp hv hs he r
  rw [← granite_local _ _ _ _ _ _ _ he r]
  by_cases hh: r≤e+2
  · exact tendsto_nhds_unique hG.played (Mending.played (Both.mended (y:= t.farY X) (δ:=fun i=> chop X (1/4) (escalates t i)) (B:= Tier S t.i) ((pursuit h hp hv hs he hh).mold (escalates t)) (fun _=> (gain_pos ..).le) (bye X t) (S.positive _)))
  have hk : ¬ Played e r:= by rintro ⟨h,k,hq⟩; omega
  let k:=escalates t 0
  have hP f : lunar X ν D (escalates t f) e r=0:= not_ne_iff.mp (mt ((X.rawStep ν D hp hv (escalates t f).cut).1.1 _ _) hk)
  apply (tendsto_nhds_unique_of_eventuallyEq hG.played tendsto_const_nhds (.of_forall hP)).trans; symm
  have hM : Whole (slate X G t.i):= (smooth h hp).again.status (fun _=> ticket_pos ..) k
  have hQ : Whole (amber X G t.i):=(polishes h hp).again.status (fun _=> ticket_pos ..) k
  exact not_ne_iff.mp (mt ((exhale_deck hM hQ (Gets_awake _ D X.kernel ν (successor t h hp hv hs)) none).1 _ _) hk)
end YM.RG08.Summit
