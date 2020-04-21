/* --------------------------------------------------------------------------------------------
 * Copyright (c) Pavel Odvody 2016
 * Licensed under the Apache-2.0 License. See License.txt in the project root for license information.
 * ------------------------------------------------------------------------------------------ */
'use strict';
import { IDependency } from './collector';
import { get_range } from './utils';
import { Diagnostic, DiagnosticSeverity, CodeAction, CodeActionKind, DocumentUri } from 'vscode-languageserver'

/* Count total # of Public and Private Vulnerability */
let Vul_public = 0;
let Vul_private = 0;

/* Descriptor describing what key-path to extract from the document */
interface IBindingDescriptor
{
    path: Array<string>;
};

/* Bind & return the part of `obj` as described by `desc` */
let bind_object = (obj: any, desc: IBindingDescriptor) => {
    let bind = obj;
    for (let elem of desc.path) {
        if (elem in bind) {
            bind = bind[elem];
        } else {
            return null;
        }
    }
    return bind;
};

/* Arbitrary metadata consumer interface */
interface IConsumer
{
    binding: IBindingDescriptor;
    item: any;
    consume(data: any): boolean;
};

/* Generic `T` producer */
interface IProducer<T>
{
    produce(ctx: any): T;
};

/* Each pipeline item is defined as a single consumer and producer pair */
interface IPipelineItem<T> extends IConsumer, IProducer<T> {}; 

/* House bunches of `IPipelineItem`'s */
interface IPipeline<T>
{
    items: Array<IPipelineItem<T>>;
    run(data: any): T;
};

/* Diagnostics producer type */
type DiagnosticProducer = IProducer<Diagnostic[]>;

/* Diagnostics pipeline implementation */
class DiagnosticsPipeline implements IPipeline<Diagnostic[]>
{
    items: Array<IPipelineItem<Diagnostic[]>>;
    dependency: IDependency;
    config: any;
    diagnostics: Array<Diagnostic>;
    uri: string;
    constructor(classes: Array<any>, dependency: IDependency, config: any, diags: Array<Diagnostic>, uri: string) {
        this.items = classes.map((i) => { return new i(dependency, config); });
        this.dependency = dependency;
        this.config = config;
        this.diagnostics = diags;
        this.uri = uri;
    }

    run(data: any): Diagnostic[] {
        for (let item of this.items) {
            if (item.consume(data)) {
                for (let d of item.produce(this.uri))
                    this.diagnostics.push(d);
            }
        }
        return this.diagnostics;
    }
};

/* A consumer that uses the binding interface to consume a metadata object */
class AnalysisConsumer implements IConsumer
{
    binding: IBindingDescriptor;
    changeToBinding: IBindingDescriptor;
    item: any;
    changeTo: string = null;
    constructor(public config: any){}
    consume(data: any): boolean {
        if (this.binding != null) {
            this.item = bind_object(data, this.binding);
        } else {
            this.item = data;
        }
        if (this.changeToBinding != null) {
            this.changeTo = bind_object(data, this.changeToBinding);
        }
        return this.item != null;
    }
};

/* We've received an empty/unfinished result, display that analysis is pending */
class EmptyResultEngine extends AnalysisConsumer implements DiagnosticProducer
{
    constructor(public context: IDependency, config: any) {
        super(config);
    }

    produce(): Diagnostic[] {
        if (this.item == {} && (this.item.finished_at === undefined ||
            this.item.finished_at == null)) {
            return [{
                severity: DiagnosticSeverity.Information,
                range: get_range(this.context.version),
                message: `Application dependency ${this.context.name.value}-${this.context.version.value} - analysis is pending`,
                source: 'Dependency Analytics '
            }]
        } else {
            return [];
        }
    }   
}

let targer_link : DocumentUri;

/* Report CVEs in found dependencies */
class SecurityEngine extends AnalysisConsumer implements DiagnosticProducer
{
    constructor(public context: IDependency, config: any) {
        super(config);
        this.binding = {path: ['recommendation']};
        /* recommendation to use a different version */
        this.changeToBinding = {path: ['recommendation', 'recommended_version']};
    }

    produce(ctx: any): Diagnostic[] {
        if (this.item != {}) {
            //let cveList = [];
            //for (let cve of this.item) {
              //  cveList.push(cve['id'])
            //}
            //let cves = cveList.join(' ');

            Vul_private += this.item.private_vulnerabilities_count;
            Vul_public += this.item.public_vulnerabilities_count;
            targer_link = this.item.registeration_link;

            let diag_severity;

            if (this.item.public_vulnerabilities_count == 0 && this.item.private_vulnerabilities_count > 0) {
                diag_severity = DiagnosticSeverity.Information; 
            } else {
                diag_severity = DiagnosticSeverity.Error;
            }

            let diagnostic = {
                severity: diag_severity,
                range: get_range(this.context.version),
                message: `${this.context.name.value} - ${this.context.version.value}`,
                source: 'Dependency Analytics ',
                code: "Find out more: 'Snyk-pkg URL'"
            };

            if (this.item.public_vulnerabilities_count == 0 && this.item.private_vulnerabilities_count > 0) {
                diagnostic.message += ` has ${this.item.private_vulnerabilities_count} security advisory by Snyk`;
            } else {
                diagnostic.message += ` has ${this.item.public_vulnerabilities_count} known security vulnerability`;
                if (this.item.private_vulnerabilities_count > 0) {
                    diagnostic.message += ` and ${this.item.private_vulnerabilities_count} security advisory by Snyk`;
                }
            }
            diagnostic.message += ` with ${this.item.exploitable_vulnerabilities_count} exploitable vulnerability and ${this.item.severity} severity.`;

            // TODO: this can be done lazily
            if (this.changeTo != null) {
                let codeAction: CodeAction = {
                    title: "Switch to recommended version " + this.changeTo,
                    diagnostics: [diagnostic],
                    kind: CodeActionKind.QuickFix,
                    edit: {
                        changes: {
                        }
                    }
                };
                codeAction.edit.changes[ctx]= [{
                    range: diagnostic.range,
                    newText: this.changeTo
                }];
                diagnostic.message += ` Recommendation: use version ${this.context.name.value} - ${this.changeTo}.`;
                codeActionsMap[diagnostic.message] = codeAction
            }
            return [diagnostic]
        } else {
            return [];
        }
    }
};

let codeActionsMap = new Map<string, CodeAction>();

let Set_default = (v1: number, v2: number) => {
    Vul_private = v1;
    Vul_public = v2;
};

export { DiagnosticsPipeline, SecurityEngine, EmptyResultEngine, codeActionsMap, Vul_private, Vul_public, Set_default };
