import YM.FullVolume.Relay.Attic
/- Unmodified Pulse output form on possibly unaligned histories. Startup. -/
set_option autoImplicit false
noncomputable section
namespace YM.FullVolume.Nectar
open RG Set Finset Filter Ray Function Amp Beam
open scoped Topology BigOperators Classical ENNReal
open MergeProof MergeProof.Accent Marker Push Push.AbsoluteSums Lattice Wilson Ac
open PhysicalNext.Repeat.Muse.Veil Orchard
variable {V I:Type} [DecidableEq V] [Fintype V] {B:Marker.Census V}{G:Gauge}{n:Side}
variable {p:BudgetPoint} (F:sun→Rep G n)(o:V→Site n)(w w':V→ℝ)(hw:∀ i,0<w i)
variable {f:sun→ Config G n→Poly B} {α:sun→ V→ Config G n→ℂ}{ωs:sun→ V→ Box n→ Config G n→ℂ}
variable (hP:∀ s,(F s).p=p)
variable {z u v W σ a c e T s t q r:ℝ}
variable (E:sun→ Support n→ Config G n→ Poly B)(K:sun→ Box n→ Config G n→Poly B) (ν:sun→ V→ℂ)
abbrev spectrum (s:sun)(x:Config G n):= Mach B (ν s)+∑ i,E s i x
abbrev singles (s:sun) (i:V) (x:Config G n):= ν s i+ ∑ j,(E s j x).part (B.fire i)
abbrev singlesK (s:sun)(i:V)(p:Box n)(x:Config G n):=(K s p x).part (B.fire i)
local notation "B_"=> spectrum E ν
variable {Q C: V→ℝ} -- single budgets
structure Proceeds (p:BudgetPoint)(f:sun→ Config G n→ Poly B) (s t:ℝ) (Q C: V→ℝ):Prop where
   realP : Refresh F o E K (spectrum E ν) (p:=p)
   ledger x:f x=oven (F x) (ν x) (E x) (K x)
   contact : Pact w id E (multiple B) p.B p.supportExponent s
   bondK : Pact w Prod.fst K (lively B) p.B p.supportExponent t
   singleE i : Treasure (fun j:Support n=> Real.exp (p.supportExponent*coverNumber p.B j)) (fun s j x=> (E s j x).part (B.fire i)) (Q i)
   singleK i : Treasure (fun j:Box n=> Real.exp (p.supportExponent*coverNumber p.B j.1)) (fun s j x=> (K s j x).part (B.fire i)) (C i)
namespace Proceeds
variable (H:Proceeds F o w E K ν p f s t Q C)
include H
private lemma inE (x:sun)(U:Config G n)(i:B.Mode): (spectrum E ν x U).part i=(Mach B (fun i=> singles E ν x i U)+∑ j, (G1 E x j U)).part i:=by
    rcases Nat.lt_trichotomy i.val.card 1 with h|h|h
    · have he:i=B.quiet:= Subtype.ext (card_eq_zero.mp (by omega)); rw [he,(H.realP.quietE x U),Poly.part_plus,mute,Poly.part_sum]; unfold G1; simp_rw [hop B _ (octaves _),sum_const_zero,zero_add]
    · obtain ⟨j,hj⟩:= card_eq_one.mp h; have he:i=B.fire j:=Subtype.ext hj; rw [he]; unfold G1 spectrum; simp_rw [Poly.part_plus, Poly.part_sum,hop₁ B _ (octaves _), sum_const_zero, sing,add_zero]
    rw [H.realP.highE x U i (by omega),Poly.part_plus,hush _ _ (by omega),zero_add]; unfold G1; simp_rw [Poly.part_sum, Accent.crest _ _ (show 2 ≤ i.val.card by omega)]
lemma indices (x:sun) : f x=restore (F x) (singles E ν x) (singlesK K x) (G1 E x) (G1 K x):=by
    rw [H.ledger]; funext U; let R:=F x
    have ht(j):K x j U=bar (F x|>.activities) B U j+Mach B (fun i=> singlesK K x i j U)+ G1 K x j U:= (ballots _).trans (by rw [H.realP.echoK x]; rfl)
    unfold oven play restore; dsimp only; congr 3
    · -- play exponent
      ext i; exact inE F o w E K ν H x U i
    -- congr!
    exact funext ht
include hw
lemma unaltered (he: q+e≤ p.supportExponent)(hc:0 ≤ c)(hg:Repegs o p.B w w' e c B)(hs:c*s≤ r)(ht:c*t≤ r): Attic B F p o w' f (singles E ν) (singlesK K) q r:=by
    have hx(s): Carton o (G1 E s) (G1 K s) p.threshold:= ⟨fun i=> ⟨(H.realP.permitE _ _).sift,fun _=>octaves _⟩,fun i=> ⟨(H.realP.permitK _ _).sift,fun _=>octaves _⟩⟩
    refine ⟨G1 E,G1 K,fun s=> ⟨hx s, indices F o w E K ν H s⟩,?_,?_⟩
    · apply Treasure.grows _ hs; exact Pact.alter hw ((H.contact.lower hw he).eighth_part (fun _ h=> h)) (fun s i=> (hx s).exp i|>.1.toBorne) (subset_refl _) hg hc
    apply Treasure.grows _ ht; exact Pact.alter hw (((H.bondK.subtype hw multiple_lively).lower hw he).eighth_part (fun _ h=> h)) (fun s i=> (hx s).flag i|>.1.toBorne) (subset_refl _) hg hc
end Proceeds
-- apply_attic base at birth. top doesn't pay incoming φ.attained bandwidth, HOT outputs all charged.
include hP hw
variable (Y:sun→ V→ Config G n→ℂ)
lemma startup_close (h:∀ x:sun,(F x).activities.Valid p σ t) (θ:sun→ V→ Response G n)(ht:∀ s i,∃ t,MergeProof.Attainment p (o i) (θ s i) t)
   (hp:∀ s j, hook (F s|>.activities) p.threshold (θ s j)=ωs s j) (v':V→ℝ) (hX:∀ i,Treasure (fun j:Support n=>Real.exp (p.supportExponent*coverNumber p.B j)) (fun t=> θ t i) (v' i))
    (hwΦ:WindowP (visaK F) Prod.fst p.B p.supportExponent W)
    (hF:∀ x i,∃ k:ℕ→ Config G n→ℂ, Dominated k ∧ ωs x i=profile (F x).activities k ∧ ∀ U, ((F x|>.eval U):ℂ)*Y x i U= Accent.coin (F x) (α x i) k U)
    (hit:∀ x U,(F x).eval U≠0) (he:p.supportExponent-1=q+e) (hc:0≤p.supportExponent-1)(hx:∑ i,w i*v' i≤ v)
    (hy:(((p.B+p.B+1:ℕ):ℝ))^4*(W+v) ≤ 1)(hd:0≤c)(hr:0≤r)(hb:Repegs o p.B w w' e c B) (ha:c*(Fintype.card V * (Real.exp (W+v)-1)) ≤ r): Attic B F p o w' (fun s=>birth B (F s) (Y s)) α ωs q r:=by
    let K(s:sun)(i:Box n):=Accent.exclaim (F s|>.activities) B i
    let E(s:sun)(i:Support n)(x:Config G n):Poly B:=0
    let X(s:sun)(U):= Mach B (fun i=>Y s i U)
    let f(s:sun):= birth B (F s) (Y s)
    have htq : Refresh F o E K X (p:=p):= by
       refine ⟨fun i j=> ⟨⟨fun _ _ _ _=>rfl,fun _ _=>rfl,fun _=>measurable_const,fun _ _ _=>rfl⟩,fun _ h=>False.elim (h rfl),fun _=>rfl⟩,fun i j=> granular _ _ _ (h _) j,fun _ _=> mute B _,fun s i U=>(Poly.part_send ..).trans (if_pos rfl),fun i U p hp=>?_⟩
       unfold E X; rw [Accent.hush _ _ hp,sum_const_zero]; rfl
    have hy1 (s U i j): (K s i U).part (B.fire j)=0:= (Poly.part_send ..).trans (if_neg (B.fire_hot _))
    apply attic_close F o w w' hw hP E K htq θ ht (fun s j i U=> by rw [hy1,zero_add, hp]) (fun s=> starting B (F s) (Y s) ((hP s).symm ▸ h s)) v' hX hwΦ (u:=0) _ (s:=0) _ h (fun x i=>?_) hit he hc hx _ hd hb _ _
    · have h : (fun s:sun => fun i:Box n × ↑(lively B) => fun U:Config G n=>(K s i.1 U).part i.2.val)=0:=funext fun _=>funext fun i=>funext fun _=> (Poly.part_send ..).trans (if_neg ((lively_ne _).1 i.2.property))
      unfold Pact; rw [h]; exact Treasure.silence
    · exact Treasure.silence -- check goal order
    · rw [add_zero]; exact hy
    · rw [mul_zero]; exact hr
    · rw [add_zero]; exact ha
    · obtain ⟨k,h,hx,hq⟩:=hF x i; exact ⟨k,h,hx,fun U=> (boot ..).trans (hq _)⟩
end YM.FullVolume.Nectar
#print axioms YM.FullVolume.Nectar.Proceeds.unaltered
#print axioms YM.FullVolume.Nectar.startup_close
