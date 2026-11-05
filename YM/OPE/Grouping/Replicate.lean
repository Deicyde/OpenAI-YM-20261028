import YM.OPE.Grouping.Birth
import YM.OPE.Grouping.Compose

/-! # Group many pairs etc along replication cells -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Ribbons.ManyCopies
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Accent Ribbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
variable {V I J Y : Type}[Fintype V][DecidableEq V][Fintype I][DecidableEq I]
  [Fintype J][DecidableEq J][Fintype Y][DecidableEq Y]{G:Gauge}{n:Side}{R:Rep G n}
  {u : (V × I)→ℂ}{a:V→Equiv.Perm V}{x:V→Site n}{m:V→Motion}{U V' : Type}

def partialGroup (V : Type) (L:Fibers I J) : Fibers (V×I) (V×J) :=
    ⟨fun i => (i.1,L.bunch i.2), fun i => (i.1,L.twig i.2), fun i=>Prod.ext rfl (L.sectioned i.2)⟩
def finishGroup (V : Type) (i:I) : Fibers (V×I) V := ⟨Prod.fst,fun v=>(v,i),fun _=>rfl⟩
def district (v:V)(I:Type) : Set (V×I) := {i| i.1=v}

lemma contentP (L:Fibers I J) (v:V)(j:J):
    ((partialGroup V L).contents (v,j))=(L.contents j).image (fun i=>(v,i)) := by
  ext i; rw [Fibers.focuses,mem_image]; constructor
  · intro h; refine ⟨i.2,(L.focuses ..).2 (congr_arg Prod.snd h),Prod.ext (congr_arg Prod.fst h).symm rfl⟩
  rintro ⟨i,hi,rfl⟩; exact Prod.ext rfl ((L.focuses ..).1 hi)
lemma contentF (v:V)(i:I):(finishGroup V i).contents v=univ.image (fun t:I=>(v,t)) := by
  ext t; rw [Fibers.focuses,mem_image]; constructor
  · intro h; exact ⟨t.2,mem_univ _,Prod.ext h.symm rfl⟩
  rintro ⟨i,-,rfl⟩; rfl

lemma district_iff (u:V)(p:(Names V I).Mode): (p.val:Set (V×I))⊆ district u I ↔ Focused u p:=by
  unfold Focused; change _↔ p.val.image _⊆{u}; rw [image_subset_iff]; simp [district, Set.subset_def]
lemma Focus_collapse {L:Fibers (V×I) Y}{s:Set Y}{v:V}(h:∀ i:V×I,L.bunch i∈s↔i∈district v I) (p:(Names V I).Mode) : L.Focus s p ↔ Focused v p:=by
  rw [← district_iff]; unfold Fibers.Focus Fibers.span; rw [coe_image,Set.image_subset_iff,show L.bunch ⁻¹' s = district v I from Set.ext h]

variable {Δ : Fibers (V×I) Y} (S : Fibers.Salt Y (V×I) Δ G n)
lemma familyOf {C G':Set Y}{b:Equiv.Perm Y} {v w:V}{a:Equiv.Perm V}{x:Site n}{m:Motion}{t:ℝ}
    (h: (Δ).Permutes (nome a) b)(hx:a v=w)
    (he:∀ i, Δ.bunch i∈C ↔ i.1=v) (he':∀ i,Δ.bunch i∈ G'↔ i.1=w)
    (hj:∀ i:I,S.grain (w,i)=affine m.1 x (S.grain (v,i)) ∧ S.pepper (w,i)=scalar m (S.pepper (v,i)))
    (hz:∀ U,(∀ i,Harm v a m (S.air i (pull m.1 x U)) (S.air (sky m x i) U))∧(∀ i,Harm v a m (S.river i (pull m.1 x U)) (S.river (puff m x i) U))) :
    Fibers.CopyFamily S t m x C G' (nome a) b := by
  refine ⟨h,fun i=>?_,?_,?_,fun p hp i U=>?_,fun p hp i U=>?_⟩
  · obtain ⟨j,rfl⟩:=Δ.sectioned.surjective i; rw [← h.run,he,he',← hx]; exact a.injective.eq_iff
  · rintro ⟨u,i⟩ hp; obtain rfl : u=v:= (he _).1 hp; rw [show nome a (u,i)=(w,i) from Prod.ext hx rfl]; exact (hj i).1
  · rintro ⟨u,i⟩ hp; obtain rfl : u=v:= (he _).1 hp; rw [show nome a (u,i)=(w,i) from Prod.ext hx rfl]; exact (hj i).2
  · exact (hz U).1 i p ((Focus_collapse (v:=v) he p).1 hp)
  exact (hz U).2 i p ((Focus_collapse (v:=v) he p).1 hp)

variable {g:(V×I) → Config G n→ℂ} {k:(V×I)→ℕ → Config G n→ℂ} {μ:(V×I)→Site n} {v:V} {P:Config G n→ Poly (Names V I)} {η T Z w c q b d α z : ℝ}
    (H : ℕ) (L:Fibers (V×I) Y) {F:(V×I)→ℝ} {C:Y→ℝ} (s l:ℕ)
set_option quotPrecheck false
local notation "τ" => R.p.threshold
local notation "y!"=> Ribbons.Salt.scent R.p.B s (R.p.supportExponent+c) T η α b
local notation "W₁"=>Fibers.Salt.tow F (R.p.supportExponent+c) (η/H) l
variable (A:Arsenal R)(hA:Arc R g k P v m x a μ F (R.p.supportExponent+c) (R.p.supportExponent+q) α b w u)
    -- use hW as in mutation, mustn't lose mirror consistency.
    (hr:R.activities.Valid R.p z d)(hP:∀ i,i≠v→∀ j:I,μ (i,j)=affine (m i).1 (x i) (μ (v,j))∧ u (i,j)=scalar (m i) (u (v,j)))
    (hw:∀ i,0<F i)(hv:Occupancy μ s)(ht:0≤T)(hy:∀ i,F i*‖u i‖ ≤ T)(hX:0<η)(hY:η≤1)(hc:0≤ c)(hq:c≤ q)
    (hH:0<H)(hF:∀ i:Y,(L.contents i).card ≤ H)(hS:∀ i:V×I,coverNumber R.p.B ({μ (L.twig (L.bunch i)),μ i}:Support n) ≤ l)
    (hit:∀ U,R.eval U≠0)(hu:∀ i,C i=∏ j∈L.contents i,Fibers.Salt.tow F (R.p.supportExponent+c) (η/H) l j)
    -- note notation hidden R, expand for variable headings later
    (hJ: ((R.p.B + R.p.B + 1 : ℕ):ℝ)^4*(Ribbons.Salt.scent R.p.B s (R.p.supportExponent+c) T η α b) ≤ c)
    (hξ: Real.exp (Ribbons.Salt.scent R.p.B s (R.p.supportExponent+c) T η α b)-1≤ Z)

include A hA hr hP hw hv ht hy hX hY hc hq hH hF hS hit hu hJ hξ
lemma publish : ∃ (k:Y→ℕ → Config G n→ℂ) (h:Support n → Config G n → Poly (Names V I)) (K:Box n → Config G n→Poly (Names V I)),
    let S : Fibers.Salt Y (V×I) L G n := ⟨μ,u,h,K⟩
    S.Birth P k C R Z ∧ Horn v m x a h K := by
  obtain ⟨F',K,ψ,hΨ,-,hF',hK,hF'',hK',hp,hZ,-,rfl⟩ := hA.see
  let S:Fibers.Salt Y (V×I) L G n:= ⟨μ,u,F',K⟩
  obtain ⟨k,hk⟩:= S.materialize s l η T Z H hH A (⟨hF'',hK'⟩:S.Breeze (τ)) hr hZ hw hv ht hy R.p.B_pos hX hY hS hc hF' (hK.shrink (by linarith only [hq]) le_rfl hw) hF hit hu hJ hξ
  exact ⟨k,F',K,hk,hp⟩

omit hF hS hu in
lemma partialFuse {L₀:Fibers I J}{C':(V×J)→ℝ} (hF:∀ i:V×J,((partialGroup V L₀).contents i).card ≤ H)
    (hS:∀ i:V×I,coverNumber R.p.B ({μ ((partialGroup V L₀).twig ((partialGroup V L₀).bunch i)),μ i}:Support n) ≤ l)
    (hu:∀ i,C' i=∏ j∈(partialGroup V L₀).contents i,W₁ j) :
    let o := μ ∘ (partialGroup V L₀).twig
    ∃ g:(V×J) → Config G n→ℂ, ∃ k:(V×J)→ℕ → Config G n→ℂ,
       Serves R g (fun i=>profile R.activities (k i)) (fun U=>Fibers.reap (partialGroup V L₀) (P U)) v m x a o C' R.p.supportExponent Z ∧
       (∀ i,Dominated (k i) ∧ Blade R (o i) (g i) (profile R.activities (k i)) 0 (4*(Z/C' i))) ∧ May v m x a g (fun i=>profile R.activities (k i)) 0 := by
  -- `omit` section vars
  obtain ⟨k,h,K,hB,hp⟩ := publish (k:=k) (g:=g) H _ s l A hA hr hP hw hv ht hy hX hY hc hq hH hF hS hit hu hJ hξ
  intro o; let Y:Fibers.Salt (V×J) (V×I) (partialGroup V L₀) G n:= ⟨μ,u,h,K⟩
  have hb:Y.Birth P k C' R Z:= hB
  have he(i:V)(hi:i≠v) : Fibers.CopyFamily Y τ (m i) (x i) (district v J) (district i J) (nome (a i)) (nome (a i)):=
    familyOf Y (default_perm (a i)) (hp i hi).1 (fun _=> Iff.rfl) (fun _=> Iff.rfl) (hP i hi) (hp i hi).2
  refine ⟨Y.debt τ,k,?_,hb.foot,?_⟩
  · refine ⟨_, _, hb.meets,hb.arc,hb.pots,fun i hi=> ⟨(hp i hi).1,fun U=> ?_⟩,hb.equal⟩
    have hK(t:(Names V J).Mode)(hz:Focused v t):= (he i hi).twines U t ((district_iff ..).2 hz)
    exact ⟨fun j=> Harps (fun p ht=> (hK p ht).1 j),fun j=> Harps (fun p ht=> (hK p ht).2 j)⟩
  intro i hi; refine ⟨(hp i hi).1,fun j =>?_⟩; have hx:= hb.travels (he i hi) (show (v,j)∈district v J from rfl); rw [show nome (a i) (v,j)=(i,j) from Prod.ext (hp i hi).1 rfl] at hx; exact ⟨hx.1,hx.2,(scalar_z _).symm⟩
where default_perm (a:Equiv.Perm V): Fibers.Permutes (partialGroup V L₀) (nome a) (nome a):=⟨fun _=>rfl,fun _=>rfl⟩

omit hF hS hu in
lemma terminalFuse {i₀:I}{C':V→ℝ} (hF:∀ i:V,((finishGroup V i₀).contents i).card ≤ H)
    (hS:∀ i:V×I,coverNumber R.p.B ({μ (i.1,i₀),μ i}:Support n) ≤ l)
    (hu:∀ i,C' i=∏ j∈(finishGroup V i₀).contents i,W₁ j) :
    let o := μ ∘ (finishGroup V i₀).twig
    ∃ g:V → Config G n→ℂ, ∃ k:V→ℕ → Config G n→ℂ,
       Served R g (fun i=>profile R.activities (k i)) (fun U=>Fibers.reap (finishGroup V i₀) (P U)) o C' R.p.supportExponent Z ∧
       (∀ i,Dominated (k i) ∧ Blade R (o i) (g i) (profile R.activities (k i)) 0 (4*(Z/C' i))) ∧
       (∀ i,i≠v→ g i=stepUp (m i) (x i) (g v) ∧
          profile R.activities (k i)=floatUp (m i) (x i) (profile R.activities (k v))) := by
  obtain ⟨k,h,K,hB,hp⟩ := publish (k:=k) (g:=g) H _ s l A hA hr hP hw hv ht hy hX hY hc hq hH hF hS hit hu hJ hξ
  intro o; let Y:Fibers.Salt V (V×I) (finishGroup V i₀) G n:= ⟨μ,u,h,K⟩
  have hb:Y.Birth P k C' R Z:= hB
  have he(i:V)(hi:i≠v) : Fibers.CopyFamily Y τ (m i) (x i) ({v}:Set V) {i} (nome (a i)) (a i) :=
    familyOf Y (default_perm (a i)) (hp i hi).1 (fun _=> Iff.rfl) (fun _=> Iff.rfl) (hP i hi) (hp i hi).2
  refine ⟨Y.debt τ,k,hb.served,hb.foot,?_⟩
  intro i hi; have hx:= hb.travels (he i hi) (Set.mem_singleton v); rw [(hp i hi).1] at hx; exact hx
where default_perm (a:Equiv.Perm V): Fibers.Permutes (finishGroup V i₀) (nome a) a:=⟨fun _=>rfl,fun _=>rfl⟩
end YM.MergeProof.Ribbons.ManyCopies
