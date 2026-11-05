import YM.RG08.Spin.Lie
/-!
# Oriented projection rule, explicitly respecting each letter slot. No masked costs. -/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Spin
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Pivot Carrier Place Scores.Pages
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{H:Hol G} {c : Side}{s:Signed}{U V:BoardU D R G}
lemma read_more (T:Hol G)(u:F.Index)(A:Finset Cham) (φ:Cham→ Exam D)(he:Toute (U e r))(hU:Polished (U e r)) : graceT T (U e r) (∑ i∈A,φ i) u=∑ i∈A, graceT T (U e r) (φ i) u:= by
    have ha i:= dapple he i; let V:=U e r
    have hp (φ: Exam D): Polished (plug φ R ∘ V):= polished_fun hU _
    have hh (p v : Exam D) : graceT T V (p+v) u=graceT T V p u+graceT T V v u:= by
       unfold graceT; rw [show plug (p+v) R ∘ V=plug p R∘ V+plug v R ∘ V from funext fun i=>by simp [plug],ladle_add T (ha _) (ha _) (hp _) (hp _),map_add,Pi.add_apply]
    classical
    induction A using Finset.induction_on with
    | empty=> rw [Finset.sum_empty,Finset.sum_empty,graceT,show plug (0:Exam D) R∘ U e r= (0: Shale (Loc G 1) r) from funext (fun i=>by simp [plug]),ladle_zero,map_zero]; rfl
    | insert a S hi IH=> rw [sum_insert hi,sum_insert hi,hh,IH]
lemma read_mark (T:Hol G)(he:Toute (U e r))(hU:Polished (U e r))(x:ℝ)(φ:Exam D)(u:F.Index) : graceT T (U e r) (x•φ) u = (x:ℂ)*graceT T (U e r) φ u := by
    unfold graceT; rw [show plug (x • φ) R ∘ U e r=x • (plug φ R ∘ U e r) from funext fun i=>by simp [plug], ladle_scale T (dapple he _) (polished_fun hU _),map_smul]; rfl
-- Read at target on turned Φ data.
lemma priory (T:Hol G)(u:F.Index)(he:Toute (U e r))(hp:Toute (V e r))(hU:Polished (U e r))(hv:Polished (V e r))(h:∀ m,Honor s U V m) (φ:Exam D):
   graceT T (U e r) φ u=
       F.act s.ortho (F.coords (ladle T (plug (twisting s φ) R ∘ V e r) d (F.grades u).2)) u := by
   unfold graceT; rw [F.act_coords,ladle_sp s T _ _ _ _ (dapple he _) (polished_fun hU _) (dapple hp _) (polished_fun hv _) (fun m=> ?_)]
   have ht:=h m (0:Site m) φ e r; simp only [Signed.act_zero] at ht; exact funext ht
lemma acts_read (u:F.Index)(v:F.Coeff) (s:Signed): F.act s.ortho v u=∑ i∈degreeT F u, (actor F s u i:ℂ)*v i := by
    have hp : v=∑ i,(v i) • Place.copy F i:= funext (fun i=>by simp [Finset.sum_apply,Place.copy,Pi.single_apply])
    conv_lhs=> rw [hp,map_sum,Finset.sum_apply]
    simp_rw [map_smul,Pi.smul_apply, pina]
    rw [← Finset.sum_subset (show degreeT F u ⊆ univ from subset_univ _) (fun i (hi:i∈univ) hx=>?_)] -- which way?
    · exact sum_congr rfl fun i _=> mul_comm ..
    · rw [thresh s u i (Ne.symm (mt ((degF u i).mpr) hx))]; simp
lemma clerk (H:Hol G)(b: Letter F)(h1:Toute (U e r))(h2:Toute (V e r))(hx:Polished (U e r))(ht:Polished (V e r))(h:∀ c, Honor s U V c)(hD:d≤D):
    invest H (U e r) b=∑ i∈(univ:Finset (Letter F)).filter (sameO b), bankO s F D b i*invest H (V e r) i:= by
    apply Complex.ofReal_injective
    rw [inserted]; push_cast
    let g:=F.grades b.label; let φ:= coinsT D b.test; let K:=bandP (cashT b.test); let X:=twisting s φ; let a i:= appoint i X; let V':= V e r
    rw [priory H _ h1 h2 hx ht h φ,acts_read]
    let y i q:= (actor F s b.label i:ℂ)*((a q:ℂ)*graceT H V' (coinsT D q) i)
    let Q i:= F.coords (ladle H (plug X R ∘ V') d g.2) i
    have hN(i:F.Index) (hi:i∈degreeT F b.label): (actor F s b.label i:ℂ)*Q i=∑ q∈K,y i q := by
        have he:= (degF ..).1 hi
        have hp:Q i=graceT H V' X i:= by unfold graceT Q g; rw [he]
        have hz:X=∑ q∈K,a q•coinsT D q:= twist_pay s _ D ((le_trans (Nat.le_add_left ..) b.bill).trans hD)
        rw [hp,hz,read_more H _ _ _ h2 ht,Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _=> by rw [read_mark H h2 ht])
    -- rewrite using spin_sum
    refine Eq.trans (Finset.sum_congr rfl hN) (spin_sum b y _ (fun i hi=> ?_))
    have hh:bankO s F D b i=actor F s b.label i.label*a i.test:= if_pos hi
    rw [hh, Complex.ofReal_mul,inserted]; unfold y; rw [mul_assoc]
-- commute full account
lemma Atlas_h (H:Hol G) (F:Labels.Frame G d)(ha:Marvel τ U)(hb: Marvel t V)(hU:Lank U)(hV:Lank V)(h:∀ c,Honor s U V c)(hD:d≤ D) :
    call H F U=fluxO s F D *ᵥ call H F V := by
    ext1 b; ext e
    let A e r:= U e r
    simp only [call,mulVec,dotProduct,map_sum,coeff_mk]
    unfold auditT
    let p i:=bankO s F D b i
    let q r i:= if slot b≤e+r then p i*invest H (V (e+r-slot b) r) i else 0
    let Z:= (Finset.univ:Finset (Letter F)).filter (sameO b)
    refine Eq.trans (b:=∑ r∈range (slot b+1),∑ i∈Z,q r i) ?_ ?_
    · refine sum_congr rfl fun r hr=> ?_; unfold q; split
      next h'=> exact clerk H b (seat_made ha) (seat_made hb) (hU _ _) (hV _ _) h hD
      next h'=> simp
    rw [Finset.sum_comm]; symm; rw [← (sum_subset (show Z⊆univ from subset_univ _) (fun j hj hx=>?_))]
    · apply Finset.sum_congr rfl; intro i hi
      have hs:= (scope_b b i).1 hi; have hX:= sameF hs
      rw [show fluxO s F D b i=PowerSeries.C (p i) from rfl, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, ← hX.2]; rw [mul_sum]; exact Finset.sum_congr rfl fun a _=> by unfold q; split; rfl; rw [mul_zero]
    have hv:= mt ((scope_b b j).2) hx; rw [fluxO,Matrix.of_apply,bankO,Matrix.of_apply,if_neg hv,map_zero,zero_mul,map_zero]
end YM.RG08.Spin
