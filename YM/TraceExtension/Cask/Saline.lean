import YM.TraceExtension.Cask.Shore
import YM.MergeProof.Temper
set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.Trace.Cask
open RG Lattice Ac MergeProof Finset MergeProof.Accent Marker MeasureTheory Wilson Push Function
open scoped Classical
variable {I V:Type}[DecidableEq I][DecidableEq V]{n:Side}[Fintype V]{G:Gauge}
variable (P:Staff V I n)
abbrev focusS (v:Duel V):= P.seat v.1
def icy (q:Stiff P)(t:ℝ)(L:Config G n→Finset I→ℂ) (U:Config G n):= shipP (crew P q.val) (blue P (L U) (flags t U) q.val)
def rob (q:TintP P)(t:ℝ)(L:Config G n→Finset I→ℂ) (U:Config G n):= shipP (crew P q.val.val) (red P (L U) (flags t U) q.val.val)
-- receipts for *averages*. depend on U only via union. word prices at WEIGHTS, no extra costs.
variable (R:Rep G n)
structure Cache (L:Config G n→ Finset I→ℂ)(w:Duel V→ℝ) (e u:ℝ):Prop where
     moves s : UsesFinal R.p.threshold (hill P s) (fun V=> L V s)
     me s : Measurable (fun V=> L V s)
     turn s : GaugeInvariant (fun V=> L V s)
     pin U s : L U s≠0→∀ i∈s,P.pole i∩flags R.p.threshold U=P.flag i
     tyre i : P.pole (i:BareP P).val=P.foot i.val
     form U (i:Finset (Stiff P)) (b:Finset (Arch P)): Haven P (flags R.p.threshold U) (beadsP i) (beadsP b) → L U (grab i b)= ∏ j∈dispel i b,L U j
     vac U p : cram (wharf P) (fun i=> L U {i.val}) p= profile R.activities (fun i=> Complex.ofReal ∘ R.activities.K i) p U
     budget : 0≤ e ∧ ∃ (ρ:ℝ)(a:I→ℝ), (∀ i,0 ≤ a i) ∧ Hit P.foot R.p.B a (e+1) ρ ∧ (((R.p.B + R.p.B +1)^4:ℕ):ℝ)*ρ ≤ 1 ∧ Real.exp ρ-1 ≤ u ∧
        ∀ s:Finset I,Spark P.foot s→ Woven P s → (crew P s).Nonempty → ∀ U:Config G n, (Poly.toll w (spanZ (crew P s))) * ‖L U s‖ ≤ ∏ i∈s,a i
variable {L:Config G n→ Finset I→ℂ}{w:Duel V→ℝ}{e u:ℝ}(C:Cache P R L w e u)
set_option quotPrecheck false
local notation "A"=> Config G n
local notation "τ"=> R.p.threshold
lemma span_woven (p:Finset I)(a:ℂ): GridApprox.Nil.Scoped ({i:Duel V| P.seat i.1∈hill P p}) (shipP (crew P p) a):= GridApprox.Nil.scope_send _ _ _ (fun i hi=> (starred P p) (mem_image_of_mem _ (mem_product.mp hi).1))
lemma span_hot (p:Finset I)(hp:(crew P p).Nonempty): 2 ≤ (spanZ (crew P p)).val.card:= by rw [spanZ,card_product]; have h:= card_pos.mpr hp; simp only [card_univ,Fintype.card_bool]; omega
lemma span_r (p:Finset I)(hp:(crew P p).Nonempty)(a:ℂ): rises (shipP (crew P p) a):=by
   intro i hi; rw[show i=spanZ (crew P p) from of_not_not (fun h=>hi (by simp[shipP,h]))]; exact span_hot P p hp
include C
lemma icy_pow (q:Stiff P): Burns (B:=Twin V) (focusS P) (hill P q.val) (icy P q τ L) τ:=by
   let X:= icy P q τ L; let F:=hill P q.val;let f:=crew P q.val; have hf:=Ice.rises P q.property
   refine ⟨⟨fun U V hu hv=> ?_,fun k U=> ?_,fun j=> ?_,fun U=> span_woven P q.val _⟩,fun U hp=>?_,fun U=>?_⟩
   · unfold icy blue; simp only [Finset.disjoint_iff_inter_eq_empty,hv,show L U _=L V _ from C.moves q.val U V hu hv]
   · unfold icy blue; rw[gauge_flags,show L (Lattice.gauge k U) _ =L U _ from C.turn q.val k U]
   · simp_rw [icy,shipP,Poly.part_send]; split; refine Measurable.ite ((healthy_closed (G:=G) τ (hill P q.val)).measurableSet) (C.me _) measurable_const; exact measurable_const
   · by_contra H; exact hp (by unfold Healthy at H; rw[icy,blue,if_neg H]; simp [shipP])
   have hv:(Twin V).quiet ≠ spanZ f:=by intro he; have hz:=span_hot P q.val hf; rw [show spanZ (crew P q.val)=_ from he.symm] at hz; simp [Census.quiet] at hz
   simp only [icy,shipP,Poly.part_send]; rw [if_neg hv]
private lemma flag_iff (q:Finset I)(U V:Config G n) (h:hill P q∩flags R.p.threshold U=hill P q∩flags R.p.threshold V): Glut P (flags τ U) q↔Glut P (flags τ V) q:=by
   apply forall_congr'; intro i; refine forall_congr' fun hi=>?_; rw [Finset.disjoint_iff_inter_eq_empty,Finset.disjoint_iff_inter_eq_empty]
   have hh: hill P i⊆hill P q:= by intro k hk; obtain ⟨j,hj,hk⟩:= mem_biUnion.mp hk; exact mem_biUnion.mpr ⟨j,(lives (sector P) _ hi).1 hj,hk⟩
   conv_lhs=> rw[← Finset.inter_eq_left.mpr hh,inter_assoc,h,← inter_assoc, Finset.inter_eq_left.mpr hh]
lemma robe_pow (q:TintP P): Flow (B:=Twin V) (focusS P) (Pier P q.val) (rob P q τ L) τ:=by
   let F:=hill P q.val.val;let f:=crew P q.val.val; have hf:= q.property
   refine ⟨⟨fun U V hu hv=> ?_,fun k U=> ?_,fun j=> ?_,fun U=> span_woven P _ _⟩,fun U hp=>?_⟩
   · have he : Glut P (flags τ U) q.val.val↔Glut P (flags τ V) q.val.val:= flag_iff P R C q.val.val U V hv
     change hill P _∩flags _ U=hill P _∩flags _ V at hv
     unfold rob red; rw [hv,he,show L U _=L V _ from C.moves q.val.val U V hu hv]
   · unfold rob red; rw[gauge_flags,show L (Lattice.gauge k U) _ =L U _ from C.turn q.val.val k U]
   · simp_rw [rob,shipP,Poly.part_send]; split; swap; exact measurable_const
     refine Measurable.ite (p:=fun U=>Glut P (flags τ U) q.val.val ∧ hill P q.val.val∩flags τ U=gem P q.val.val) ?_ (C.me _) measurable_const
     -- finite possible flags
     have he:{U:A|Glut P (flags τ U) q.val.val∧hill P q.val.val∩flags τ U=gem P q.val.val}=
             ⋃ p:{p:Support n//Glut P p q.val.val∧hill P q.val.val∩p=gem P q.val.val}, {U:A|flags τ U=p.val}:=by
          ext x; rw[Set.mem_iUnion]; constructor; intro hp; exact ⟨⟨_,hp⟩,rfl⟩
          rintro ⟨v,hv⟩; change Glut P (flags τ x) _ ∧ hill _ _ ∩ flags τ x=gem _ _; exact ((show flags τ x=v.val from hv).symm ▸ v.property)
     rw [he]; exact MeasurableSet.iUnion (fun _=>flags_measurable_eq ..)
   have he: Glut P (flags τ U) q.val.val∧hill P q.val.val∩flags τ U=gem P q.val.val:=of_not_not (fun h=> hp (by rw [rob,red,if_neg h]; simp [shipP]))
   exact ⟨he.2,⟨q.val.property.wet,owns ..⟩⟩
omit C
lemma pegs_l (w:Duel V→ℝ)(hw:∀ i,0<w i)(v:Finset I)(F:A→ℂ)(s:ℝ)(hs:0 ≤ s)(H:∀ U, Poly.toll w (spanZ (crew P v))*‖F U‖ ≤ s): Loci w (fun U=>shipP (crew P v) (F U)) s:=by
    let m:= spanZ (crew P v); let w':=Poly.toll w m; have hh:0 < w':= Poly.worth hw _
    refine ⟨fun i=> if i=m then s/w' else 0,fun i=> by change 0 ≤ if i=m then s/w' else 0; split; exact div_nonneg hs hh.le; exact le_rfl,fun U i=> ?_,?_⟩
    · simp only[shipP,Poly.part_send]; change ‖(if i=m then F U else 0)‖ ≤ if i=m then s/w' else 0; split; exact (le_div_iff₀ hh).mpr ((mul_comm ..).trans_le (H U)); simp
    apply le_of_eq; unfold GridApprox.Nil.wordsPrice; rw [sum_eq_single m]; simp only[↓reduceIte]; exact mul_div_cancel₀ _ hh.ne'
    · intro b _ hb; simp [hb]
    simp
include C
variable [Fintype I]
lemma sails (hw:∀ i,0<w i): Towed w (hill P ∘ Subtype.val) (fun i:Stiff P=> icy P i τ L) R.p.B e u ∧ Towed w (fun i:TintP P=>hill P i.val.val) (fun i:TintP P=>rob P i τ L) R.p.B e u:=by
   obtain ⟨he,ρ,a,ha,hA,hv,hρ,H⟩:= C.budget
   let v:=fun s:Finset I=>∏ i∈s,a i; have hp: 0≤ρ:= Planned.GuardedAtom.sumBudget_credit (hA 0)
   have hx (p:Finset I) : 0 ≤ v p:=prod_nonneg fun i _=>ha i
   have ht {X:Type}[Fintype X](p:X→Finset I)(hi:Injective p)(hx':∀ i,Spark P.foot (p i)) (q:X→A→ℂ) (h:∀ i,∀ U,Poly.toll w (spanZ (crew P (p i)))*‖q i U‖ ≤ v (p i)): Towed w (hill P ∘ p) (fun i U=>shipP (crew P (p i)) (q i U)) R.p.B e u:=by
       refine ⟨v ∘ p,Summable.of_finite,fun i=>?_,fun i=>pegs_l P w hw _ _ _ (hx _) (h i)⟩
       have hu:= Ac.forest P.foot R.p.B he ha hA (by exact_mod_cast hv) hp i
       have h': SumBudget (fun j=> if i∈hill P (p j) then v (p j)*Real.exp (e*coverNumber R.p.B (hill P (p j))) else 0) (Real.exp ρ-1):=by
           refine Extra.Multi.Budget.pull_le (q:=p) (p:=fun _=>True) hu (fun i=> by split; exact mul_nonneg (hx _) (Real.exp_pos _).le; exact le_rfl) (fun _ _=>trivial) hi.injOn (fun j _=> ?_)
           by_cases H:i∈hill P (p j)
           · rw[if_pos H,Ac.roots,if_pos ⟨hx' j,H⟩]; exact (mul_comm ..).le
           exact (if_neg H).le.trans (hu.1 _)
       exact ⟨h'.1,h'.2.1,h'.2.2.trans hρ⟩
   constructor
   · refine ht Subtype.val Subtype.val_injective (fun i:Stiff P=>Ice.moving P i.property) (fun i U=>blue P (L U) (flags τ U) i.val) (fun i U=>?_); unfold blue; split; exact H _ (Ice.moving P i.property) i.property.sound (Ice.rises P i.property) U; simpa using hx i.val
   refine ht (fun i:TintP P=> i.val.val) (Subtype.val_injective.comp Subtype.val_injective) (fun i=> i.val.property.force) (fun i U=> red P (L U) (flags τ U) i.val.val) (fun i U=>?_); unfold red; split; exact H _ i.val.property.force i.val.property.sound i.property U; simpa using hx i.val.val
def shore (P:Staff V I n) (R:Rep G n) (L:Config G n→Finset I→ℂ)(U:A): Poly (Twin V):= (Real.exp (R.exponent U):ℂ) • ∑ q, swarm P (L U) (flags R.p.threshold U) q
lemma Cache.presents (hw:∀ i,0<w i): Served R 0 0 (shore P R L) (focusS P) w e u:=by
    obtain ⟨Hx,Hy⟩:= sails P R C hw; let f:Stiff P→Support n:= hill P ∘ Subtype.val; let b:TintP P→Box n:=Pier P ∘ Subtype.val
    let Q(i):= icy P i τ L; let K(i):=rob P i τ L; let X:= tally f Q; let Y:= tally b K
    have hf(i): Burns (B:=Twin V) (focusS P) (f i) (Q i) τ:= icy_pow P R C _;have hb(i): Flow (B:=Twin V) (focusS P) (b i) (K i) τ:= robe_pow P R C _
    have hr{I J:Type}[Fintype I] (f:I→J)(F:I→A→Poly (Twin V))(h:∀ i U, rises (F i U))(j U): rises (tally f F j U):=by
       intro s hx; by_contra h'; unfold tally at hx; rw[Poly.share Summable.of_finite] at hx
       exact hx ((tsum_congr (fun i=> Classical.byContradiction fun ht=> h' (h i.val U s ht))).trans tsum_zero)
    refine ⟨X,Y,⟨fun i=> ⟨transitE f (r:=id) hf (fun _=>Summable.of_finite) _, fun U=> hr f Q (fun k _=> span_r P _ (Ice.rises P k.property) _) i U⟩,fun i=> ⟨transitK b (r:=id) hb (fun _=>Summable.of_finite) _, fun U=> hr b K (fun k _=>span_r P _ k.property _) i U⟩⟩,towing (r:=id) f Q Hx hw,towing (r:=Prod.fst) b K Hy hw,?_⟩
    funext U; rw [shore,restore]; apply congr_arg (_ • ·); have hh:Mach (Twin V) (fun _=>0)=0:=by simp [Mach]
    change _=Poly.pass (_+_)*Accent.field _ _; simp only [Pi.zero_apply,hh,zero_add,add_zero]
    let p:=flags τ U; have he(i:Box n): cargo P p (L U) i= bar R.activities (Twin V) U i+Y i U:=by
       rw [soft_p P p _ C.tyre (fun _=>C.pin U _) i,C.vac]; rfl
    refine (emerge P p _ (C.pin U) (C.form U)).symm.trans ?_
    apply congr_arg₂ _ rfl; change Accent.field (cargo P p (L U)) p=_; exact congr_arg (fun f=> Accent.field f p) (funext he)
end YM.Trace.Cask
