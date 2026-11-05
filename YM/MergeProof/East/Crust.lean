import YM.MergeProof.East.Glaze
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Consumer

set_option autoImplicit false
noncomputable section
namespace YM.Next.Rank.East
open Function Filter RG Labels Source.Drops Source Thirst Baler Lattice Wilson Corona Value Glyph Marker Perch Vac.Numbers Alarm Station Cells Spindle Atlas Edition Normal LiftMark Rise MvPolynomial Configuration
open scoped BigOperators Classical Topology Matrix.Norms.Frobenius ContDiff
open Further.CorrectedLift.Compass
variable {G:Gauge}{C:Family G} {k d p W n m N b:ℕ}
local notation "A"=> C.path.levels
lemma half_wind (s:Signed)(u:PlaqAxes):wind s u=1 ∨ wind s u = -1:=by apply eq_or_eq_neg_of_sq_eq_sq; rw [pow_two,wind_sq,one_pow]
lemma norm_wind (s:Signed)(u:PlaqAxes): ‖wind s u‖=1:=(half_wind s u).elim (fun h=>by rw [h];simp) fun h=>by rw [h];simp

def pivot (s:Signed)(i:slotC G b) := Finsupp.single (swing s i.1,i.2) ((wind s i.1.val.2:ℝ):ℂ)
lemma cheaper (s:Signed)(P:poly (slotC G b)): coin (exchange (pivot s) P) ≤ coin P:= by
    refine (rise (pivot s) _ zero_le_one le_rfl (fun i=> ?_) P le_rfl).trans (by rw [one_pow,mul_one])
    unfold pivot; rw [glyph,Finsupp.linearCombination_single]; apply (peak_cost 1 _ _ _ zero_le_one).trans; simp only [pay_X,one_pow,mul_one,Complex.norm_real,norm_wind];rfl
lemma phased (s:Signed)(Y:Turn b→G.Color)(P:poly (slotC G b)) :
    text (fun i:slotC G b=>Y i.1 i.2) (exchange (pivot s) P)= text (fun i:slotC G b=> (wind s i.1.val.2 • Y (swing s i.1)) i.2) P:=by
    apply DFunLike.congr_fun (f:=(aeval (R:=ℂ) _).comp (exchange (pivot s))); ext1 i; rw [AlgHom.comp_apply,exchange_x,aeval_X]; unfold pivot; rw [glyph,Finsupp.linearCombination_single,map_smul,aeval_X]; simp
lemma wreath (s:Signed)(P:poly (slotC G b))(h:Spirit P): Spirit (exchange (pivot s) P):=by
    intro u i; rw [phased,phased]
    unfold coloring; simp_rw [← _root_.map_smul]; exact h (fun j=> wind s j.val.2 • u (swing s j)) i

open PhysicalNext PhysicalNext.RankCovariance
local notation "Xa" => control (k:=k) (RankCovariance.stamp A N p) 0 W
def collar (r : 4*b ≤ W) (X : Normal.Symmetric (trimV W G)) := scope (fun i:slotC G b=>Finsupp.single (calls r i) 1) X
lemma pearl (r: 4*b≤W)(X : Normal.Symmetric (trimV W G))(P : poly (slotC G b)):
    milk X (rename (calls r) P) = rename (calls r) (milk (collar r X) P):=by rw [Normal.labelled]; exact Normal.prepared ..
lemma treats_wind (B:Binding C)(h:k ≤ N)(r: 4*b ≤ W) (s:Signed): scope (pivot s) (collar r (control (k:=k) (RankCovariance.stamp A N p) 0 W))=collar r Xa:=by
    let X:= control (k:=k) (RankCovariance.stamp C.path.levels N p) 0 W
    let φ:=collar r X
    let D:= C.side k p; let κ:= ((RankCovariance.stamp C.path.levels N p).κ k).cov; let F(i:slotC G b):= ((wrap D i.1.val.1,i.1.val.2,i.2):Incidence G D)
    have he(i j): φ.cov i j=κ (F i) (F j) := by
        unfold φ collar X;rw [match_name,Atlas.control,match_name]; simp only [body,zero_add];rfl
    apply Normal.Symmetric.ext; funext i j
    let P(i:slotC G b):=(swing s i.1,i.2)
    have hp:= RankCovariance.signed_cash A N k p B.world B.present B.pays h s (F i) (F j)
    dsimp only at hp
    have hv (j): Face.send s 0 ((F j).1,(F j).2.1)=((F (P j)).1, (F (P j)).2.1):=prize D s j.1
    rw [hv,hv] at hp
    change treats φ (pivot s i) (pivot s j)=φ.cov i j
    rw [he]; apply Eq.trans _ hp; unfold treats pivot; simp only [Finsupp.linearCombination_single, Pi.smul_apply,smul_eq_mul]; rw [he]; simp only [Complex.ofReal_mul]; dsimp only [κ,F,P]; ring_nf

private lemma glow_set (H:Hol G)(s:Signed)(r: 4*b ≤ W)(P:poly (slotC G b))(d)(J: Jet G):
    let F:= fun p:poly (slotC G b)=>Rise.trim (printed0 r d p) (key G d) d
    let T:=changedJet (fun _=>Taylor.turn s.ortho⁻¹) J
    aeval (kp d (Drops.trunk d J)) (F (exchange (pivot s) P)) = aeval (kp d (Drops.trunk d T)) (F P):=by
    intro F T
    dsimp only [F]; rw [← ray_stamp,← ray_stamp]; apply congr_arg (fun p=> evaluate_ray p d); funext t
    rw [writes_color, writes_color, phased]; apply congr_arg (fun x=> text x P); funext i
    let L:=Drops.trunk d J
    have hs: Spindle.flash (Drops.trunk d T) t=turning s d G (Spindle.flash (Drops.trunk d J) t):=by
       funext x; change Spindle.flash (Drops.trunk d T) t x = Taylor.turn s.ortho⁻¹ (Spindle.flash L t x)
       simp only [L,T,Spindle.flash, Drops.trunk,scaleJet,Drops.expand, dif_pos x.isLt,changedJet]
       exact (map_smul (Taylor.turn s.ortho⁻¹) (t^(x.val+2)) _).symm
    rw [hs,lustre H]
private lemma licence (Q:poly (KeyIn G d))(J:Jet G) : Labels.read J (rename (Subtype.val : KeyIn G d→Key G) Q)=aeval (kp d (Drops.trunk d J)) Q:=by
    apply DFunLike.congr_fun (f:=(Labels.read J).comp (rename Subtype.val)); ext1 i; rw [aeval_X]
    have h : i.val.1<d-1 := (spanKey d i).isLt
    simp only [AlgHom.comp_apply, Labels.read,kp,Labels.coord,Drops.expand, Drops.trunk,dif_pos h,rename_X,aeval_X]

lemma stamp_at (B:Binding C)(h:k ≤ N)(r: 4*b ≤ W) (s:Signed)(P:poly (slotC G b))(F : Label G d)
    (hp: Perch.Verdict Subtype.val d (milk Xa (rename (calls r) P)) F): Perch.Verdict Subtype.val d (milk Xa (rename (calls r) (exchange (pivot s) P))) (Labels.tensor s.ortho F):=by
    unfold Perch.Verdict at *
    rw [LiftMark.costs,pearl] at hp; rw [LiftMark.costs,pearl,Normal.prepared,treats_wind B h r s]
    let X:= Subtype.val (p:=fun i=> i∈strip W G); let φ:=collar r Xa;let Y:=milk φ P; let f:=fun p:poly (slotC G b)=> Rise.trim (printed0 r d p) (key G d) d
    have hh: f Y= thawKey F:= MvPolynomial.rename_injective (R:=ℂ) (f:=Sum.inl) Sum.inl_injective hp
    apply congr_arg; apply MvPolynomial.rename_injective (R:=ℂ) (Subtype.val : KeyIn G d→Key G) Subtype.val_injective
    rw [Configuration.returns]; apply Labels.eval_ext; intro J
    let K:=exchange (pivot s) Y
    change Labels.read J (rename _ (f K))= Labels.read J (Labels.rotated s.ortho F.val)
    rw [licence,show aeval (kp d _) (f K)=_ from glow_set C.params s r Y d J, Labels.rotated,Labels.eval_changed]
    change aeval _ (f Y)= _; rw [hh,← licence]; rw [Configuration.returns]
end YM.Next.Rank.East
